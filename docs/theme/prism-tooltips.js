// Static typed tooltips. `prism mdbook` embeds the canonical
// prism-typespans-v1 payload and nested spans; this tiny consumer only handles
// interaction. A future wasm analyzer can hand the same schema to `bind` after
// rendering an editable block—there is deliberately no second browser format.
(function () {
  "use strict";

  var FORMAT = "prism-typespans-v1";
  var tooltip = null;
  var active = null;

  function payloadOf(code) {
    var raw = code && code.getAttribute("data-typespans");
    if (!raw) return null;
    try {
      var payload = JSON.parse(raw);
      return payload && payload.format === FORMAT && Array.isArray(payload.spans)
        ? payload
        : null;
    } catch (_) {
      return null;
    }
  }

  function ensureTooltip() {
    if (tooltip) return tooltip;
    tooltip = document.createElement("div");
    tooltip.className = "prism-type-tooltip";
    tooltip.setAttribute("role", "tooltip");
    tooltip.hidden = true;
    document.body.appendChild(tooltip);
    return tooltip;
  }

  function hide() {
    if (active) active.classList.remove("prism-type-active");
    active = null;
    if (tooltip) tooltip.hidden = true;
  }

  // Non-value levels get a labeled prefix and their own bubble styling.
  var LEVEL_PREFIX = {
    typelevel: "Typelevel: ",
    class: "Type Class: ",
    typevar: "Type Variable: ",
    effect: "Effect: ",
    coeffect: "Coeffect: ",
    hole: "Inferred Type Hole: ",
    patternvar: "Pattern Variable: ",
    logic: "Logic Expression: ",
  };

  function show(span) {
    if (!span || span === active) return;
    hide();
    active = span;
    active.classList.add("prism-type-active");
    var bubble = ensureTooltip();
    var level = span.getAttribute("data-level") || "";
    var prefix = LEVEL_PREFIX[level] || "";
    bubble.textContent = "";
    if (prefix) {
      var label = document.createElement("span");
      label.className = "prism-tooltip-label";
      label.textContent = prefix;
      bubble.appendChild(label);
    }
    bubble.appendChild(
      document.createTextNode(span.getAttribute("data-type") || "")
    );
    bubble.className =
      "prism-type-tooltip" + (level ? " prism-type-tooltip-" + level : "");
    bubble.hidden = false;
    var rect = span.getBoundingClientRect();
    var tip = bubble.getBoundingClientRect();
    var left = rect.left + rect.width / 2 - tip.width / 2;
    left = Math.max(8, Math.min(left, window.innerWidth - tip.width - 8));
    var top = rect.top - tip.height - 8;
    if (top < 8) top = rect.bottom + 8;
    bubble.style.left = left + "px";
    bubble.style.top = top + "px";
  }

  function nearest(target) {
    return target && target.closest && target.closest(".prism-type-span");
  }

  function bind(root) {
    (root || document).querySelectorAll("code.prism-typed").forEach(function (code) {
      if (code.dataset.prismTypesBound || !payloadOf(code)) return;
      code.dataset.prismTypesBound = "1";
      code.addEventListener("mouseover", function (event) {
        show(nearest(event.target));
      });
      code.addEventListener("mouseout", function (event) {
        var next = nearest(event.relatedTarget);
        if (!next || !code.contains(next)) hide();
      });
      code.addEventListener("focusin", function (event) {
        show(nearest(event.target));
      });
      code.addEventListener("focusout", function (event) {
        if (!code.contains(event.relatedTarget)) hide();
      });
    });
  }

  window.PrismTypeTooltips = { FORMAT: FORMAT, bind: bind, payloadOf: payloadOf };
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", function () { bind(document); });
  } else {
    bind(document);
  }
})();
