/-
Language toggle button shared by the Spanish and English builds.

Both sites are deployed together: Spanish at the site root and English under
`en/`. Every Verso page carries a `<base href>` pointing at its own build's
root, so the script can locate the current page relative to its language root
and jump to the same page in the other language. If that page does not exist
there (e.g. a chapter that is not translated yet), it falls back to the
closest existing ancestor page, and finally to the other language's home page.

Pages must use the same `file :=` slug in both languages for the mapping to
work (see the `%%%` metadata blocks in `Docs/` and `DocsEn/`).
-/
import VersoManual

open Verso.Output
open Verso.Output.Html

namespace Docs

def langToggleCss : String := r#"
#lang-toggle {
  position: fixed;
  top: 0.65rem;
  right: 0.85rem;
  z-index: 10000;
  display: inline-flex;
  align-items: center;
  gap: 0.45em;
  padding: 0.45em 1.1em;
  border-radius: 999px;
  background: #205ea6;
  color: #ffffff;
  font-family: inherit;
  font-size: 0.95rem;
  font-weight: 600;
  text-decoration: none;
  box-shadow: 0 2px 8px rgba(0, 0, 0, 0.35);
  cursor: pointer;
  transition: background 0.15s ease;
}
#lang-toggle:hover {
  background: #2d77cc;
  color: #ffffff;
  text-decoration: none;
}
@media (max-width: 700px) {
  #lang-toggle {
    top: auto;
    bottom: 1rem;
  }
}
"#

def langToggleJsBody : String := r#"
(function () {
  function init() {
    var root = new URL(document.baseURI);
    var isEs = VERSO_LANG === 'es';
    var other = isEs ? new URL('en/', root) : new URL('../', root);
    var btn = document.createElement('a');
    btn.id = 'lang-toggle';
    btn.href = other.href;
    btn.textContent = isEs ? '🌐 English' : '🌐 Español';
    btn.title = isEs ? 'Read this page in English' : 'Leer esta página en español';
    btn.addEventListener('click', function (ev) {
      ev.preventDefault();
      go();
    });
    document.body.appendChild(btn);

    function go() {
      var path = window.location.pathname;
      var rel = path.indexOf(root.pathname) === 0 ? path.slice(root.pathname.length) : '';
      var parts = rel.split('/').filter(function (p) { return p.length > 0; });
      if (parts.length > 0 && parts[parts.length - 1] === 'index.html') {
        parts.pop();
      }
      tryNext();
      function tryNext() {
        if (parts.length === 0) {
          window.location.href = other.href;
          return;
        }
        var candidate = new URL(parts.join('/') + '/', other);
        fetch(candidate.href, { method: 'HEAD' })
          .then(function (r) {
            if (r.ok) {
              window.location.href = candidate.href;
            } else {
              parts.pop();
              tryNext();
            }
          })
          .catch(function () {
            window.location.href = other.href;
          });
      }
    }
  }
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();
"#

def langToggleJs (current : String) : String :=
  s!"var VERSO_LANG = '{current}';\n" ++ langToggleJsBody

/--
Head elements (style + script) that add the language toggle button to every
page. `current` is the language of the build this is included in: `"es"` or
`"en"`.
-/
def langToggle (current : String) : Array Html := #[
  {{<style>{{Html.text false langToggleCss}}</style>}},
  {{<script>{{Html.text false (langToggleJs current)}}</script>}}
]

end Docs
