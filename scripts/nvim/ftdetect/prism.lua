-- Prism filetype detection: map *.pr to the `prism` filetype. Loaded eagerly
-- at startup so the matching syntax/prism.lua is sourced when a buffer's syntax
-- is set. See scripts/nvim/syntax/prism.lua for the highlighter itself.
vim.filetype.add({ extension = { pr = "prism" } })
