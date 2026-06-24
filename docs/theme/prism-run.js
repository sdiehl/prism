// Make every ```prism block in the docs runnable in-browser, via the same
// wasm interpreter the playground uses (the parity oracle, so output matches
// native). The wasm bundle is served at ./pkg/ alongside the book; it is
// lazy-loaded on the first Run click and cached for the session.
(function () {
  var ready = null; // Promise<module>, created on first use.

  // Inline SVGs (no icon-font dependency): a filled play triangle for Run, an
  // external-link glyph for opening the standalone playground.
  var ICON_RUN =
    '<svg class="prism-run-ico" viewBox="0 0 24 24" width="13" height="13" fill="currentColor" aria-hidden="true"><path d="M8 5v14l11-7z"/></svg>';
  var ICON_OPEN =
    '<svg class="prism-run-ico" viewBox="0 0 24 24" width="13" height="13" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M15 3h6v6"/><path d="M10 14 21 3"/><path d="M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h6"/></svg>';

  function loadWasm() {
    if (!ready) {
      // This script is served from /theme/; dynamic import resolves relative to
      // it, so "../pkg" reaches the /pkg bundle (and clamps to /pkg from the
      // document base too, so it is robust either way).
      ready = import("../pkg/prism.js").then(function (m) {
        return m.default().then(function () {
          return m;
        });
      });
    }
    return ready;
  }

  function playgroundHref(source) {
    // Deep-link the standalone playground with the source in the URL fragment.
    // UTF-8-safe base64: encode to bytes, then btoa over a binary string.
    var bytes = new TextEncoder().encode(source);
    var bin = "";
    for (var i = 0; i < bytes.length; i++) bin += String.fromCharCode(bytes[i]);
    return "play/#code=" + encodeURIComponent(btoa(bin));
  }

  function enhance(code) {
    var pre = code.parentNode; // <pre>
    if (!pre || pre.dataset.prismRun) return;
    pre.dataset.prismRun = "1";

    var bar = document.createElement("div");
    bar.className = "prism-run-bar";

    var runBtn = document.createElement("button");
    runBtn.className = "prism-run-btn";
    runBtn.type = "button";
    runBtn.innerHTML = ICON_RUN + '<span class="prism-run-label">Run</span>';
    var runLabel = runBtn.querySelector(".prism-run-label");

    var open = document.createElement("a");
    open.className = "prism-run-btn prism-run-open";
    open.target = "_blank";
    open.rel = "noopener";
    open.href = playgroundHref(code.textContent);
    open.innerHTML = ICON_OPEN + "<span>Open in Playground</span>";

    bar.appendChild(runBtn);
    bar.appendChild(open);

    var output = document.createElement("pre");
    output.className = "prism-run-out";
    output.hidden = true;

    pre.parentNode.insertBefore(bar, pre.nextSibling);
    pre.parentNode.insertBefore(output, bar.nextSibling);

    runBtn.addEventListener("click", function () {
      runBtn.disabled = true;
      runLabel.textContent = "Running";
      output.hidden = false;
      output.textContent = "";
      output.classList.remove("prism-run-err");
      loadWasm().then(
        function (m) {
          var result;
          try {
            result = m.run(code.textContent);
          } catch (e) {
            result = "error: " + ((e && e.message) || e);
          }
          var isErr = /^error:/.test(result);
          output.textContent = result === "" ? "(no output)" : result;
          output.classList.toggle("prism-run-err", isErr);
          runBtn.disabled = false;
          runLabel.textContent = "Run";
        },
        function (e) {
          output.textContent =
            "could not load the interpreter: " + ((e && e.message) || e);
          output.classList.add("prism-run-err");
          runBtn.disabled = false;
          runLabel.textContent = "Run";
        }
      );
    });
  }

  function enhanceAll() {
    document.querySelectorAll("pre code.language-prism").forEach(enhance);
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", enhanceAll);
  } else {
    enhanceAll();
  }
})();
