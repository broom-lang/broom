let failat span what ?msg =
    (match (span, msg) with
    | (Some span, Some msg) -> what ^ ": " ^ msg ^ " at " ^ Util.span_to_string span
    | (Some span, None) -> what ^ " at " ^ Util.span_to_string span
    | (None, Some msg) -> what ^ ": " ^ msg
    | (None, None) -> what)
    |> failwith

let unreachable ?msg span = failat span "unreachable" ?msg
let todo ?msg span = failat span "TODO" ?msg
let bug ?msg span = failat span "compiler bug" ?msg

