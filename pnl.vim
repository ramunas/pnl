if exists("b:current_syntax")
    finish
endif
let b:current_syntax="pnl"

syn keyword PNLTodo contained TODO FIXME XXX NOTE
syn match PNLComment "#.*$" contains=PNLTodo
syn match PNLVar "`\s*\w\+"
" syn match Type ":\s*\w\+"
" syn region PNLType start=":"hs=e+1 end="fn\|name\|var\|rw"he=s-1 contains=PNLKeywords

syn match PNLOp "=>"
syn match PNLOp "==>"
syn match PNLOp ":"

syn keyword PNLKeywords fn rw type nametype name var sos term
" syn keyword PNLOp =>

hi def link PNLKeywords   Keyword
hi def link PNLOp   Operator
hi def link PNLComment Comment
hi def link PNLTodo Todo
hi def link PNLVar Special
hi def link PNLType Type
