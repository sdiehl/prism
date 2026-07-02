// Render each ```prism block by what the compiler makes of it. The `prism`
// mdbook preprocessor (see `prism mdbook`) live-checks every block and stamps a
// kind and status onto the fence, which mdbook turns into CSS classes on the
// `<code>`: `run`/`check`/`norun`/`cfail` with `ok`/`err`, plus `sig`/`def`/
// `ignore`. This script reads those classes and shows the matching control:
//
//   run,ok    green Run button (runs in-browser, via the same wasm interpreter
//             the playground uses, so output matches native) + Open in Playground
//   check,ok  green check: the block type-checks but is not a whole program
//   norun,ok  ghosted Run button: it compiles, but is not run here
//   cfail,ok  amber check: it is expected to fail to type-check
//   *,err     red cross: a block that should type-check does not
//   sig       a bare type signature
//   ignore    grey check: not checked
//   def       a declaration; rendered plain, no control
//
// A `language-prism` block with none of these classes (e.g. built without the
// preprocessor) falls back to a plain Run button.
(function () {
  var ready = null; // Promise<module>, created on first use.

  var ICON_RUN =
    '<svg class="prism-run-ico" viewBox="0 0 24 24" width="13" height="13" fill="currentColor" aria-hidden="true"><path d="M8 5v14l11-7z"/></svg>';
  var ICON_OPEN =
    '<svg class="prism-run-ico" viewBox="0 0 24 24" width="13" height="13" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M15 3h6v6"/><path d="M10 14 21 3"/><path d="M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h6"/></svg>';
  var ICON_CHECK =
    '<svg class="prism-run-ico" viewBox="0 0 24 24" width="13" height="13" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 6 9 17l-5-5"/></svg>';
  var ICON_CROSS =
    '<svg class="prism-run-ico" viewBox="0 0 24 24" width="13" height="13" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M18 6 6 18M6 6l12 12"/></svg>';

  function loadWasm() {
    if (!ready) {
      ready = import("../pkg/prism.js").then(function (m) {
        return m.default().then(function () {
          return m;
        });
      });
    }
    return ready;
  }

  function playgroundHref(source) {
    var bytes = new TextEncoder().encode(source);
    var bin = "";
    for (var i = 0; i < bytes.length; i++) bin += String.fromCharCode(bytes[i]);
    return "play/#code=" + encodeURIComponent(btoa(bin));
  }

  // The full content hash a reference block carries, as an `h-<hex>` class, or
  // null. Rendered as a subdued pill beside the block's Σ badge (short prefix
  // shown, full hash copied on click).
  function hashOf(cl) {
    for (var i = 0; i < cl.length; i++) {
      var m = /^h-([0-9a-f]+)$/.exec(cl[i]);
      if (m) return m[1];
    }
    return null;
  }

  function copyText(text) {
    if (navigator.clipboard && navigator.clipboard.writeText) {
      return navigator.clipboard.writeText(text);
    }
    var ta = document.createElement("textarea");
    ta.value = text;
    ta.style.position = "fixed";
    ta.style.opacity = "0";
    document.body.appendChild(ta);
    ta.select();
    try {
      document.execCommand("copy");
    } catch (e) {}
    document.body.removeChild(ta);
    return Promise.resolve();
  }

  // Copy `full` to the clipboard on click, flashing a brief "Copied" confirmation
  // (a `data-tip` swap plus the `.prism-copied` class the CSS makes visible).
  function makeCopyable(el, full) {
    el.classList.add("prism-copyable");
    el.addEventListener("click", function () {
      copyText(full).then(function () {
        var prev = el.getAttribute("data-tip");
        el.setAttribute("data-tip", "Copied");
        el.classList.add("prism-copied");
        setTimeout(function () {
          el.classList.remove("prism-copied");
          if (prev === null) el.removeAttribute("data-tip");
          else el.setAttribute("data-tip", prev);
        }, 1100);
      });
    });
  }

  function kindOf(cl) {
    if (cl.contains("sig")) return "sig";
    if (cl.contains("def")) return "def";
    if (cl.contains("ignore")) return "ignore";
    if (cl.contains("err")) return "err";
    if (cl.contains("cfail")) return "cfail";
    if (cl.contains("norun")) return "norun";
    if (cl.contains("check")) return "check";
    return "run"; // `run`, or an unprocessed block
  }

  // An icon-only status badge; the description shows as a tooltip on hover
  // (a styled bubble via CSS `data-tip`, plus `aria-label` for screen readers).
  function chip(kind, icon, title) {
    var bar = document.createElement("div");
    bar.className = "prism-run-bar";
    var c = document.createElement("span");
    c.className = "prism-chip prism-chip-" + kind;
    c.setAttribute("data-tip", title);
    c.setAttribute("aria-label", title);
    c.innerHTML = icon;
    bar.appendChild(c);
    return bar;
  }

  // A Run bar (active or ghosted) plus its output pane and Open-in-Playground.
  function runBar(code, ghost, title) {
    var bar = document.createElement("div");
    bar.className = "prism-run-bar";

    var runBtn = document.createElement("button");
    runBtn.className = "prism-run-btn" + (ghost ? " prism-run-ghost" : "");
    runBtn.type = "button";
    runBtn.disabled = ghost;
    if (ghost) runBtn.title = title;
    runBtn.innerHTML =
      ICON_RUN + '<span class="prism-run-label">' + (ghost ? "Not run" : "Run") + "</span>";
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

    if (!ghost) {
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
    return { bar: bar, output: output };
  }

  function enhance(code) {
    var pre = code.parentNode; // <pre>
    if (!pre || pre.dataset.prismRun) return;
    pre.dataset.prismRun = "1";

    var kind = kindOf(code.classList);

    var after = null; // element(s) to insert after the <pre>
    var tail = null;
    if (kind === "run" || kind === "norun") {
      var r = runBar(code, kind === "norun", "This example compiles, but is not run here");
      after = r.bar;
      tail = r.output;
    } else if (kind === "check") {
      after = chip("check", ICON_CHECK, "Type-checks");
    } else if (kind === "cfail") {
      after = chip("cfail", ICON_CHECK, "Expected to fail to type-check");
    } else if (kind === "ignore") {
      after = chip("ignore", ICON_CHECK, "Not type-checked");
    } else if (kind === "err") {
      after = chip("err", ICON_CROSS, "Does not type-check");
    } else if (kind === "sig") {
      after = chip("sig", "Σ", "Type signature");
    } else if (kind === "def") {
      after = chip("sig", "Σ", "Verbatim from code");
    }

    // A reference block may also carry a content hash: a quiet monospace pill
    // sitting next to its Σ badge in the same bar.
    var h = hashOf(code.classList);
    if (after && h && (kind === "sig" || kind === "def")) {
      var pill = document.createElement("span");
      pill.className = "prism-chip prism-hash";
      pill.setAttribute("data-tip", "Copy content hash");
      pill.setAttribute("aria-label", "Content hash " + h + ", click to copy");
      pill.textContent = h.slice(0, 8);
      makeCopyable(pill, h);
      after.appendChild(pill);
    }

    if (after) pre.parentNode.insertBefore(after, pre.nextSibling);
    if (tail) pre.parentNode.insertBefore(tail, after.nextSibling);
  }

  function enhanceAll() {
    document.querySelectorAll("pre code.language-prism").forEach(enhance);
    // Static copyable elements authored in the page (the index Merkle root).
    document.querySelectorAll("[data-copy]").forEach(function (el) {
      if (!el.dataset.prismCopy) {
        el.dataset.prismCopy = "1";
        makeCopyable(el, el.getAttribute("data-copy"));
      }
    });
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", enhanceAll);
  } else {
    enhanceAll();
  }
})();
