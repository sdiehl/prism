-- Prism syntax highlighting for Neovim.
--
-- A classic vim-syntax highlighter (keyword/match/region rules linked to the
-- standard groups your colorscheme already styles). The token set mirrors the
-- lexer in src/lex/token.rs, so keywords stay in sync with the compiler.
--
-- This file lives in a `syntax/` runtime dir on purpose: Neovim's syntax loader
-- sources it (after `syntax clear`) whenever a buffer's filetype is `prism`,
-- which a `plugin/`-level FileType autocmd cannot do reliably (the loader's
-- clear runs after the autocmd and wipes it). Filetype detection lives next door
-- in ftdetect/prism.lua.

-- Re-entrant guard: the loader may source this more than once per buffer.
if vim.b.current_syntax then
  return
end

local cmd = vim.cmd

-- Declarations and binding forms.
cmd([[syntax keyword prismKeyword let var in val return do borrow with handler given where as forall deriving of handle using]])
cmd([[syntax keyword prismInclude import pub]])
cmd([[syntax keyword prismStructure fn fip fbip replayable type newtype opaque alias effect class instance canonical pattern]])
cmd([[syntax keyword prismConditional if then else elif match]])
cmd([[syntax keyword prismRepeat for while loop break continue]])
-- Effect control and failure forms.
cmd([[syntax keyword prismException throw try catch transact mask error]])
cmd([[syntax keyword prismBoolean true false]])

-- Builtin scalar types and effect/handler verbs that are ordinary identifiers
-- in the lexer but read as language vocabulary.
cmd([[syntax keyword prismType Int Bool Unit Float Char String I64 U64]])
cmd([[syntax keyword prismBuiltin resume emit perform fail guard succeeds optional default print println eprint eprintln each]])

-- Uppercase identifiers are constructors / type names; a dotted uppercase head
-- is a qualified module path.
cmd([[syntax match prismModule "\<[A-Z][A-Za-z0-9_]*\.\%([A-Za-z_][A-Za-z0-9_]*\)\+\>"]])
cmd([[syntax match prismConstructor "\<[A-Z][A-Za-z0-9_]*\>"]])

-- Literals.
cmd([[syntax match prismFloat "\<[0-9]\+\.[0-9]\+\>"]])
cmd([[syntax match prismNumber "\<[0-9]\+\%(i64\|u64\)\?\>"]])
cmd([[syntax match prismCharacter "'\%(\\.\|[^'\\]\)'"]])
cmd([[syntax region prismString start=+"+ skip=+\\.+ end=+"+ contains=prismStringEscape]])
cmd([[syntax match prismStringEscape "\\." contained]])

-- Operators: arrows, the effect bang, pipes, dot-chaining, var assign, failure
-- fallback / optional chaining, and arithmetic/comparison.
cmd([[syntax match prismOperator "\%(->\|<-\|=>\|:=\|??\|?\.\|>>\|<<\|||\||>\|&&\|==\.\?\|/=\.\?\|<=\.\?\|>=\.\?\|[-+*/%<>=!|?.^~]\)"]])

-- Line comments, with the usual TODO/FIXME callouts.
cmd([[syntax keyword prismTodo TODO FIXME XXX NOTE contained]])
cmd([[syntax match prismComment "--.*$" contains=prismTodo]])

-- Link to standard groups so any colorscheme styles them.
local link = function(from, to)
  cmd(string.format("highlight default link %s %s", from, to))
end
link("prismKeyword", "Keyword")
link("prismInclude", "Include")
link("prismStructure", "Structure")
link("prismConditional", "Conditional")
link("prismRepeat", "Repeat")
link("prismException", "Exception")
link("prismBoolean", "Boolean")
link("prismType", "Type")
link("prismBuiltin", "Special")
link("prismModule", "Include")
link("prismConstructor", "Type")
link("prismFloat", "Float")
link("prismNumber", "Number")
link("prismCharacter", "Character")
link("prismString", "String")
link("prismStringEscape", "SpecialChar")
link("prismOperator", "Operator")
link("prismComment", "Comment")
link("prismTodo", "Todo")

vim.bo.commentstring = "-- %s"
vim.b.current_syntax = "prism"
