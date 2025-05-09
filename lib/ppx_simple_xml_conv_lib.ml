open! Core
module Xml = Simple_xml

module Of_xml = struct
  module Namespace = struct
    type t =
      | Do_not_care
      | Assert_no_namespace
      | Assert_equals of string
    [@@deriving sexp_of, compare]

    let namespace_matches t namespace =
      match t with
      | Do_not_care -> true
      | Assert_no_namespace -> String.is_empty namespace
      | Assert_equals ns -> String.equal ns namespace
    ;;
  end

  type 'a element =
    { tag : string
    ; namespace : Namespace.t
    ; parse : Xml.element -> 'a
    }

  type 'a t =
    | Element of 'a element
    | Variant of 'a element list lazy_t

  module Element_count = struct
    type (_, _) t =
      | Required : ('a, 'a) t
      | Option : ('a, 'a option) t
      | List : ('a, 'a list) t
      | Default : 'a -> ('a, 'a) t
  end

  module Attribute_count = struct
    type (_, _) t =
      | Required : ('a, 'a) t
      | Option : ('a, 'a option) t
      | Default : 'a -> ('a, 'a) t
  end

  module Element_container = struct
    module type S = sig
      type 'a t

      val of_list : 'a list -> 'a t
      val return : 'a -> 'a t
      val is_empty : 'a t -> bool
      val map_into_list : 'a t -> f:('a -> 'b) -> 'b list
      val extract : 'a t -> f:('a -> bool) -> 'a list
      val extract_map : 'a t -> f:('a -> 'b option) -> 'b list
    end

    module Option_array_based : S = struct
      type 'a t = 'a option array

      let fold_righti t ~init ~f =
        let acc = ref init in
        for i = Array.length t - 1 downto 0 do
          match Array.unsafe_get t i with
          | Some v -> acc := f i !acc v
          | None -> ()
        done;
        !acc
      ;;

      let unsafe_set_none t i = Array.unsafe_set t i None
      let of_list list = Array.of_list_map list ~f:Option.return
      let return value = [| Some value |]
      let is_empty t = Array.for_all t ~f:Option.is_none

      let extract t ~f =
        fold_righti t ~init:[] ~f:(fun i result element ->
          if f element
          then (
            unsafe_set_none t i;
            element :: result)
          else result)
      ;;

      let extract_map t ~f =
        fold_righti t ~init:[] ~f:(fun i result element ->
          match f element with
          | Some element ->
            unsafe_set_none t i;
            element :: result
          | None -> result)
      ;;

      let map_into_list t ~f =
        fold_righti t ~init:[] ~f:(fun _ acc value -> f value :: acc)
      ;;
    end

    include Option_array_based
  end

  type 'a inlined =
    Xml.element Element_container.t
    -> Xml.Attribute.t list
    -> 'a * Xml.element Element_container.t * Xml.Attribute.t list

  let with_ns ~ns value =
    match ns with
    | "" -> value
    | ns -> [%string "%{value}[namespace=%{ns}]"]
  ;;

  let check_no_extra_attributes attributes : unit =
    let extra_attributes =
      List.filter attributes ~f:(fun attribute ->
        not (String.equal attribute.Xml.Attribute.ns Xmlm.ns_xmlns))
    in
    if not (List.is_empty extra_attributes)
    then
      failwithf
        "Ppx_simple_xml_conv: extra attributes: %s"
        (List.map extra_attributes ~f:(fun attribute ->
           with_ns ~ns:attribute.ns attribute.key)
         |> String.concat ~sep:", ")
        ()
  ;;

  let check_no_extra_children children : unit =
    if not (Element_container.is_empty children)
    then
      failwithf
        "Ppx_simple_xml_conv: extra elements: %s"
        (Element_container.map_into_list children ~f:(fun { Xml.tag; _ } ->
           with_ns ~ns:tag.ns tag.tag)
         |> String.concat ~sep:", ")
        ()
  ;;

  let elements_only (xmls : Xml.t list) =
    List.filter_map xmls ~f:(function
      | Element element -> Some element
      | Text _ -> None)
    |> Element_container.of_list
  ;;

  type 'output parser_and_constructor =
    | Parser_and_constructor :
        { parse : 'a t
        ; construct : 'a -> 'output
        }
        -> 'output parser_and_constructor

  let flatten_variants parsers_and_constructors =
    let lift_parse parse ~f element = parse element |> f in
    let parsers =
      lazy
        (List.concat_map
           parsers_and_constructors
           ~f:(fun (Parser_and_constructor { parse; construct }) ->
             match parse with
             | Element { tag; namespace; parse } ->
               [ { tag; namespace; parse = lift_parse parse ~f:construct } ]
             | Variant parsers ->
               List.map (Lazy.force parsers) ~f:(fun { tag; namespace; parse } ->
                 { tag; namespace; parse = lift_parse parse ~f:construct })))
    in
    Variant parsers
  ;;

  let simple_convert ?(ignore_attributes = false) ~namespace tag ~f =
    Element
      { tag
      ; parse =
          (fun element ->
            let result = f element.children in
            if not ignore_attributes then check_no_extra_attributes element.attributes;
            result)
      ; namespace
      }
  ;;

  let extract_text ?(preserve_space = false) ~tag = function
    | [] -> ""
    | [ Xml.Text text ] -> if preserve_space then text else String.strip text
    | children ->
      raise_s
        [%message
          "Did not expect child elements, got child elements"
            (tag : string)
            (children : Xml.t list)]
  ;;

  let leaf
    ?ignore_attributes
    ?preserve_space
    ?(namespace = Namespace.Do_not_care)
    tag
    ~of_string
    =
    simple_convert ~namespace ?ignore_attributes tag ~f:(fun children ->
      extract_text ?preserve_space ~tag children |> of_string)
  ;;

  let empty_element
    ?ignore_attributes
    ?(ignore_children = false)
    ?(namespace = Namespace.Do_not_care)
    tag
    =
    simple_convert
      ?ignore_attributes
      ~namespace
      tag
      ~f:
        (if ignore_children
         then (ignore : Xml.t list -> unit)
         else
           fun children ->
           match extract_text ~tag children with
           | "" -> ()
           | contents ->
             raise_s
               [%message
                 "Expected empty tag, tag not empty" (tag : string) (contents : string)])
  ;;

  let with_element_count
    (type input output)
    (count : (input, output) Element_count.t)
    ~element_description
    matching
    ~(f : _ -> input)
    : output
    =
    match count, matching with
    | Required, [ child ] -> f child
    | Required, matching ->
      failwithf
        "Ppx_simple_xml_conv: Expected 1 instance of %s, got %d"
        (Lazy.force element_description)
        (List.length matching)
        ()
    | Option, [] -> None
    | Option, [ child ] -> Some (f child)
    | Option, matching ->
      failwithf
        "Ppx_simple_xml_conv: Expected 0 or 1 instances of %s, got %d"
        (Lazy.force element_description)
        (List.length matching)
        ()
    | List, children -> List.map children ~f
    | Default default, [] -> default
    | Default _, [ child ] -> f child
    | Default _, matching ->
      failwithf
        "Ppx_simple_xml_conv: Expected 0 or 1 instances of %s, got %d"
        (Lazy.force element_description)
        (List.length matching)
        ()
  ;;

  let description ~tag ~namespace =
    match (namespace : Namespace.t) with
    | Do_not_care -> tag
    | Assert_no_namespace -> [%string "%{tag}[no namespace]"]
    | Assert_equals ns -> [%string "%{tag}[namespace=%{ns}]"]
  ;;

  let variant_parser count parsers elements =
    let element_description =
      lazy
        (List.map parsers ~f:(fun parser ->
           description ~tag:parser.tag ~namespace:parser.namespace)
         |> String.concat ~sep:" or ")
    in
    let find_parser (element : Xml.element) =
      List.find_map parsers ~f:(fun { tag; namespace; parse } ->
        if String.equal element.tag.tag tag
           && Namespace.namespace_matches namespace element.tag.ns
        then Some (parse, element)
        else None)
    in
    let matching = Element_container.extract_map elements ~f:find_parser in
    let parsed =
      with_element_count count ~element_description matching ~f:(fun (parse, element) ->
        parse element)
    in
    parsed, elements
  ;;

  let element count children (converter : 'input t)
    : 'output * Xml.element Element_container.t
    =
    match converter with
    | Element { tag; namespace; parse } ->
      let matching =
        Element_container.extract children ~f:(fun (element : Xml.element) ->
          String.equal tag element.tag.tag
          && Namespace.namespace_matches namespace element.tag.ns)
      in
      let parsed =
        with_element_count
          count
          ~element_description:(lazy (description ~tag ~namespace))
          matching
          ~f:parse
      in
      parsed, children
    | Variant tags -> variant_parser count (Lazy.force tags) children
  ;;

  let extract_attribute attributes key_to_extract ~namespace =
    let rec loop ~acc = function
      | [] -> None, attributes
      | ({ Xml.Attribute.key; ns; _ } as entry) :: rest ->
        if String.equal key_to_extract key && Namespace.namespace_matches namespace ns
        then Some entry, List.rev_append acc rest
        else loop ~acc:(entry :: acc) rest
    in
    loop ~acc:[] attributes
  ;;

  let attribute
    (type input output)
    (count : (input, output) Attribute_count.t)
    attributes
    ~(of_string : string -> input)
    ~namespace
    ~key
    =
    let attribute, rest = extract_attribute attributes key ~namespace in
    let parse attribute = of_string attribute.Xml.Attribute.value in
    let parsed : output =
      match count, attribute with
      | Required, Some attribute -> parse attribute
      | Required, None -> failwithf "Ppx_simple_xml_conv: Attribute %s missing" key ()
      | Option, attribute -> Option.map attribute ~f:parse
      | Default default, attribute -> Option.value_map attribute ~default ~f:parse
    in
    parsed, rest
  ;;

  let parse t element_to_parse =
    element Required (Element_container.return element_to_parse) t |> fst
  ;;

  let lift_element (element_parser : 'a element) ~f =
    { element_parser with parse = (fun element -> element_parser.parse element |> f) }
  ;;

  let lift (t : 'a t) ~f =
    match t with
    | Element element -> Element (lift_element ~f element)
    | Variant variants ->
      Variant
        (let%map.Lazy variants in
         List.map variants ~f:(lift_element ~f))
  ;;

  let lift_inlined (inlined : 'a inlined) ~f container attributes =
    let result, container, attributes = inlined container attributes in
    f result, container, attributes
  ;;

  let override_parse t ~f =
    match t with
    | Element { tag; namespace; parse } ->
      Element { tag; namespace; parse = f ~namespace ~tag parse }
    | Variant variants ->
      Variant
        (let%map.Lazy variants in
         List.map variants ~f:(fun { tag; namespace; parse } ->
           { tag; namespace; parse = f ~namespace ~tag parse }))
  ;;

  include
    Ppx_simple_xml_conv_lib_intf.Signatures.Of_xml
      (struct
        type nonrec 'a t = 'a t
      end)
      (struct
        type 'a t = 'a inlined
      end)

  module Of_xmlable
      (M : S)
      (Target : sig
         type t

         val of_xmlable : M.t -> t
       end) : S with type t := Target.t = struct
    let t_of_xml_description = lift M.t_of_xml_description ~f:Target.of_xmlable
    let t_of_xml element = parse t_of_xml_description element
  end

  module Of_xmlable1
      (M : S1)
      (Target : sig
         type 'a t

         val of_xmlable : 'a M.t -> 'a t
       end) : S1 with type 'a t := 'a Target.t = struct
    let t_of_xml_description a_of_xml_description =
      lift (M.t_of_xml_description a_of_xml_description) ~f:Target.of_xmlable
    ;;

    let t_of_xml a_of_xml_description element =
      parse (t_of_xml_description a_of_xml_description) element
    ;;
  end

  module Of_xmlable2
      (M : S2)
      (Target : sig
         type ('a, 'b) t

         val of_xmlable : ('a, 'b) M.t -> ('a, 'b) t
       end) : S2 with type ('a, 'b) t := ('a, 'b) Target.t = struct
    let t_of_xml_description a_of_xml_description b_of_xml_description =
      lift
        (M.t_of_xml_description a_of_xml_description b_of_xml_description)
        ~f:Target.of_xmlable
    ;;

    let t_of_xml a_of_xml_description b_of_xml_description element =
      parse (t_of_xml_description a_of_xml_description b_of_xml_description) element
    ;;
  end

  module Inlined = struct
    include Inlined

    module Of_xmlable
        (M : S)
        (Target : sig
           type t

           val of_xmlable : M.t -> t
         end) : S with type t := Target.t = struct
      let t_of_xml_inlined = lift_inlined M.t_of_xml_inlined ~f:Target.of_xmlable
    end

    module Of_xmlable1
        (M : S1)
        (Target : sig
           type 'a t

           val of_xmlable : 'a M.t -> 'a t
         end) : S1 with type 'a t := 'a Target.t = struct
      let t_of_xml_inlined a_of_xml_description =
        lift_inlined (M.t_of_xml_inlined a_of_xml_description) ~f:Target.of_xmlable
      ;;
    end

    module Of_xmlable2
        (M : S2)
        (Target : sig
           type ('a, 'b) t

           val of_xmlable : ('a, 'b) M.t -> ('a, 'b) t
         end) : S2 with type ('a, 'b) t := ('a, 'b) Target.t = struct
      let t_of_xml_inlined a_of_xml_description b_of_xml_description =
        lift_inlined
          (M.t_of_xml_inlined a_of_xml_description b_of_xml_description)
          ~f:Target.of_xmlable
      ;;
    end
  end
end

module To_xml = struct
  module Builder = struct
    let prepend_list xs ~convert rest = List.rev_append (List.rev_map xs ~f:convert) rest
    let prepend x ~convert rest = convert x :: rest

    let prepend_opt x ~convert rest =
      match x with
      | None -> rest
      | Some x -> prepend x ~convert rest
    ;;

    let xmlns_namespace = Xmlm.ns_xmlns
  end

  type 'a inlined = 'a -> Xml.t list * Xml.Attribute.t list

  include Ppx_simple_xml_conv_lib_intf.Signatures.To_xml (struct
      type 'a t = 'a inlined
    end)

  module Of_xmlable
      (M : S)
      (Target : sig
         type t

         val to_xmlable : t -> M.t
       end) : S with type t := Target.t = struct
    let xml_of_t t = Target.to_xmlable t |> M.xml_of_t
  end

  module Of_xmlable1
      (M : S1)
      (Target : sig
         type 'a t

         val to_xmlable : 'a t -> 'a M.t
       end) : S1 with type 'a t := 'a Target.t = struct
    let xml_of_t xml_of_a t = Target.to_xmlable t |> M.xml_of_t xml_of_a
  end

  module Of_xmlable2
      (M : S2)
      (Target : sig
         type ('a, 'b) t

         val to_xmlable : ('a, 'b) t -> ('a, 'b) M.t
       end) : S2 with type ('a, 'b) t := ('a, 'b) Target.t = struct
    let xml_of_t xml_of_a xml_of_b t = Target.to_xmlable t |> M.xml_of_t xml_of_a xml_of_b
  end

  module Inlined = struct
    include Inlined

    module Of_xmlable
        (M : S)
        (Target : sig
           type t

           val to_xmlable : t -> M.t
         end) : S with type t := Target.t = struct
      let inlined_xml_of_t t = Target.to_xmlable t |> M.inlined_xml_of_t
    end

    module Of_xmlable1
        (M : S1)
        (Target : sig
           type 'a t

           val to_xmlable : 'a t -> 'a M.t
         end) : S1 with type 'a t := 'a Target.t = struct
      let inlined_xml_of_t xml_of_a t = Target.to_xmlable t |> M.inlined_xml_of_t xml_of_a
    end

    module Of_xmlable2
        (M : S2)
        (Target : sig
           type ('a, 'b) t

           val to_xmlable : ('a, 'b) t -> ('a, 'b) M.t
         end) : S2 with type ('a, 'b) t := ('a, 'b) Target.t = struct
      let inlined_xml_of_t xml_of_a xml_of_b t =
        Target.to_xmlable t |> M.inlined_xml_of_t xml_of_a xml_of_b
      ;;
    end
  end
end

include
  Ppx_simple_xml_conv_lib_intf.Signatures.Make
    (Of_xml)
    (struct
      type 'a t = 'a Of_xml.inlined
    end)
    (struct
      type 'a t = 'a To_xml.inlined
    end)

module Of_xmlable
    (M : S)
    (Target : sig
       type t

       val to_xmlable : t -> M.t
       val of_xmlable : M.t -> t
     end) : S with type t := Target.t = struct
  include To_xml.Of_xmlable (M) (Target)
  include Of_xml.Of_xmlable (M) (Target)
end

module Of_xmlable1
    (M : S1)
    (Target : sig
       type 'a t

       val to_xmlable : 'a t -> 'a M.t
       val of_xmlable : 'a M.t -> 'a t
     end) : S1 with type 'a t := 'a Target.t = struct
  include To_xml.Of_xmlable1 (M) (Target)
  include Of_xml.Of_xmlable1 (M) (Target)
end

module Of_xmlable2
    (M : S2)
    (Target : sig
       type ('a, 'b) t

       val to_xmlable : ('a, 'b) t -> ('a, 'b) M.t
       val of_xmlable : ('a, 'b) M.t -> ('a, 'b) t
     end) : S2 with type ('a, 'b) t := ('a, 'b) Target.t = struct
  include To_xml.Of_xmlable2 (M) (Target)
  include Of_xml.Of_xmlable2 (M) (Target)
end

module Inlined = struct
  include Inlined

  module Of_xmlable
      (M : S)
      (Target : sig
         type t

         val to_xmlable : t -> M.t
         val of_xmlable : M.t -> t
       end) : S with type t := Target.t = struct
    include To_xml.Inlined.Of_xmlable (M) (Target)
    include Of_xml.Inlined.Of_xmlable (M) (Target)
  end

  module Of_xmlable1
      (M : S1)
      (Target : sig
         type 'a t

         val to_xmlable : 'a t -> 'a M.t
         val of_xmlable : 'a M.t -> 'a t
       end) : S1 with type 'a t := 'a Target.t = struct
    include To_xml.Inlined.Of_xmlable1 (M) (Target)
    include Of_xml.Inlined.Of_xmlable1 (M) (Target)
  end

  module Of_xmlable2
      (M : S2)
      (Target : sig
         type ('a, 'b) t

         val to_xmlable : ('a, 'b) t -> ('a, 'b) M.t
         val of_xmlable : ('a, 'b) M.t -> ('a, 'b) t
       end) : S2 with type ('a, 'b) t := ('a, 'b) Target.t = struct
    include To_xml.Inlined.Of_xmlable2 (M) (Target)
    include Of_xml.Inlined.Of_xmlable2 (M) (Target)
  end
end

module Primitives = struct
  let string_of_string x = x
  let string_to_string x = x
  let int_to_string = Int.to_string
  let float_to_string = Float.to_string

  let result_of_xml_description ok_of_xml_description error_of_xml_description =
    Of_xml.flatten_variants
      [ Parser_and_constructor
          { parse = ok_of_xml_description; construct = (fun x -> Ok x) }
      ; Parser_and_constructor
          { parse = error_of_xml_description; construct = (fun x -> Error x) }
      ]
  ;;

  let result_of_xml ok_of_xml error_of_xml xml =
    Of_xml.parse (result_of_xml_description ok_of_xml error_of_xml) xml
  ;;

  let xml_of_result ok_to_xml error_to_xml = function
    | Ok x -> ok_to_xml x
    | Error x -> error_to_xml x
  ;;
end
