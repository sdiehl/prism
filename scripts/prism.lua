-- Prism syntax highlighting for Neovim
--
-- Install: copy or symlink this file into a runtimepath plugin dir, e.g.
--   ln -s "$PWD/scripts/prism.lua" ~/.config/nvim/plugin/prism.lua
-- or load it on demand from your config with
--   dofile("/path/to/prism/scripts/prism.lua")
--
-- It registers the `prism` filetype for `*.pr` files and installs a classic
-- vim-syntax highlighter (keyword/match/region rules linked to the standard
-- groups your colorscheme already styles). The token set mirrors the lexer in
-- src/lex/token.rs, so keywords stay in sync with the compiler.

-- Filetype detection for .pr sources.
vim.filetype.add({ extension = { pr = "prism" } })

local function highlight()
  -- Re-entrant guard: FileType can fire more than once per buffer.
  if vim.b.current_syntax then
    return
  end

  local cmd = vim.cmd

  -- Declarations and binding forms.
  cmd([[syntax keyword prismKeyword let var in fun val return do borrow with handler given where as forall deriving of handle]])
  cmd([[syntax keyword prismInclude import pub]])
  cmd([[syntax keyword prismStructure fn fip fbip type newtype opaque alias effect class instance pattern]])
  cmd([[syntax keyword prismConditional if then else elif match]])
  cmd([[syntax keyword prismRepeat for]])
  -- Effect control and failure forms.
  cmd([[syntax keyword prismException throw try catch transact mask final ctl error]])
  cmd([[syntax keyword prismBoolean true false]])

  -- Builtin scalar types and effect/handler verbs that are ordinary
  -- identifiers in the lexer but read as language vocabulary.
  cmd([[syntax keyword prismType Int Bool Unit Float Char String I64 U64]])
  cmd([[syntax keyword prismBuiltin resume emit perform fail guard succeeds optional default print println eprint eprintln]])

  -- Uppercase identifiers are constructors / type names; a dotted uppercase
  -- head is a qualified module path.
  cmd([[syntax match prismModule "\<[A-Z][A-Za-z0-9_]*\.\%([A-Za-z_][A-Za-z0-9_]*\)\+\>"]])
  cmd([[syntax match prismConstructor "\<[A-Z][A-Za-z0-9_]*\>"]])

  -- Literals.
  cmd([[syntax match prismFloat "\<[0-9]\+\.[0-9]\+\>"]])
  cmd([[syntax match prismNumber "\<[0-9]\+\%(i64\|u64\)\?\>"]])
  cmd([[syntax match prismCharacter "'\%(\\.\|[^'\\]\)'"]])
  cmd([[syntax region prismString start=+"+ skip=+\\.+ end=+"+ contains=prismStringEscape]])
  cmd([[syntax match prismStringEscape "\\." contained]])

  -- Operators: arrows, the effect bang, pipes, dot-chaining, var assign,
  -- failure fallback / optional chaining, and arithmetic/comparison.
  cmd([[syntax match prismOperator "\%(->\|<-\|=>\|:=\|??\|?\.\|>>\|<<\|||\||>\|&&\|==\.\?\|/=\.\?\|<=\.\?\|>=\.\?\|[-+*/%<>=!|?.]\)"]])

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
end

vim.api.nvim_create_autocmd("FileType", {
  pattern = "prism",
  callback = highlight,
  desc = "Prism syntax highlighting",
})
