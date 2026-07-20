// Register Prism as a highlight.js language. mdbook ships highlight.js but has
// no grammar for `prism`, so ```prism blocks render unstyled. additional-js can
// load before or after mdbook's highlight.js, so we poll for the `hljs` global,
// then register the language (keywords mirror src/lex/token.rs) and highlight
// every prism block. The keyword set mirrors src/lex/token.rs.
(function () {
  function define() {
    if (window.__prismHljsDone) return;
    window.__prismHljsDone = true;
    hljs.registerLanguage("prism", function (hl) {
      return {
        name: "Prism",
        keywords: {
          keyword:
            "fn fip fbip replayable pub import as type newtype opaque effect error throw " +
            "try catch transact alias class instance canonical pattern deriving where " +
            "given handle with handler mask ctl final fun val return let var " +
            "borrow in for while loop break continue do if then else elif match of " +
            "each forall using stable probe logic requires ensures total assume",
          literal: "true false",
          type: "Int Bool Unit Float Char String I64 U64",
        },
        contains: [
          hl.COMMENT("--", "$"),
          { className: "string", begin: '"', end: '"', contains: [{ begin: "\\\\." }] },
          { className: "string", begin: "'", end: "'", contains: [{ begin: "\\\\." }] },
          hl.C_NUMBER_MODE,
          // Any capitalized identifier: builtin/user types, data constructors,
          // effect and class names. `hljs-title.class` (a v11 nested-scope
          // spelling) isn't a real class the shipped ayu theme styles, so this
          // colors them the same as the builtin `type:` keywords above.
          { className: "type", begin: "\\b[A-Z][A-Za-z0-9_]*" },
        ],
      };
    });
    // mdbook ships highlight.js 10.x (highlightBlock); 11.x uses
    // highlightElement. Support both. The block was left unstyled by mdbook
    // (prism was unknown then), so its textContent is the raw source.
    var paint = hljs.highlightElement || hljs.highlightBlock;
    document.querySelectorAll("code.language-prism").forEach(function (el) {
      // Successfully checked blocks were already tokenized by the compiler and carry
      // nested type ranges. Re-highlighting would replace that checked HTML.
      if (el.classList.contains("prism-typed")) return;
      paint.call(hljs, el);
    });
  }

  var tries = 0;
  (function poll() {
    if (typeof hljs !== "undefined" && hljs.registerLanguage) {
      define();
    } else if (tries++ < 100) {
      setTimeout(poll, 30);
    }
  })();
})();
