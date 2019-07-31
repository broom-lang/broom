* A statement is either a definition or an expression
* Any type is a valid expression
* Any expression is a valid type
* Any expression is a valid pattern
    - Except for parameter patterns where arrow types have to be parenthesized

* So we don't really need `expr` and `typ` nonterminals, we need stmt vs. param
  patterns
