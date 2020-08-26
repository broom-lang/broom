if exists('b:current_syntax')
    finish
endif

syntax keyword broomKeyword extends override exclude let begin end val fun type match when where with without effect
highlight default link broomKeyword Keyword

syntax match broomColon ":"
highlight default link broomColon Operator
syntax match broomEq '='
highlight default link broomEq Operator
syntax match broomArrow "->"
highlight default link broomArrow Operator
syntax match broomEffow "-!"
highlight default link broomEffow Operator
syntax match broomDArrow "=>"
highlight default link broomDArrow Operator
syntax match broomBang "!"
highlight default link broomBang Operator
syntax match broomBar "|"
highlight default link broomBar Operator
syntax match broomImplicitly '@'
highlight default link broomImplicitly Operator

syntax match broomIntrinsic '__\w\+'
highlight default link broomIntrinsic PreProc

syntax region broomString start=/"/ end=/"/
highlight default link broomString String

syntax region broomLineComment start=/--/ end=/\n/
highlight default link broomLineComment Comment

let b:current_syntax = 'broom'

