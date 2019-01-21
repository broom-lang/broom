functor FType(type var) = struct
    datatype prim = I32

    datatype kind = ArrowK of Pos.t * {domain: kind, codomain: kind}
                  | TypeK of Pos.t

    type def = {var: var, kind: kind}

    datatype 'typ typ = ForAll of Pos.t * def * 'typ
                      | Arrow of Pos.t * {domain: 'typ, codomain: 'typ}
                      | UseT of Pos.t * def
                      | Prim of Pos.t * prim
end
