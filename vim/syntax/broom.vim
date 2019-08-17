if exists('b:current_syntax')
    finish
endif

syntax keyword broomKeyword begin module interface do return end val fun type pi forall match when
highlight default link broomKeyword Keyword

syntax match broomColon ":"
highlight default link broomColon Operator
syntax match broomEq '='
highlight default link broomEq Operator
syntax match broomArrow "->"
highlight default link broomArrow Operator
syntax match broomDArrow "=>"
highlight default link broomDArrow Operator

syntax match broomMacro '@\w\+'
highlight default link broomMacro PreProc

syntax match broomIntrinsic '__\w\+'
highlight default link broomIntrinsic PreProc

syntax region broomString start=/"/ end=/"/
highlight default link broomString String

syntax region broomLineComment start=/#/ end=/\n/
highlight default link broomLineComment Comment

let b:current_syntax = 'broom'

