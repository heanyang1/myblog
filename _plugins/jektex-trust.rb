# frozen_string_literal: true

# KaTeX trust mode, so that math may contain \href{...}{...}.
#
# numbering.rb turns \ref{...}/\eqref{...} inside math into \href links to
# the labelled spot, but KaTeX only honours \href (and \url, \htmlId, ...)
# when the `trust` option is set, and jektex 0.1.1 calls
# katex.renderToString with fixed options (displayMode and macros only).
#
# So recompile jektex's bundled katex.min.js with a small wrapper appended
# that injects `trust: true` into every render call, and swap the result in
# for jektex's KATEX ExecJS context. Swapping the constant (rather than
# calling KATEX.exec) matters because execjs's external runtimes start a
# fresh JS process for every call: state set via #exec would not persist.
# Recompiling from the pristine file keeps the swap idempotent across
# `jekyll serve` rebuilds. Only author-written content is ever rendered, so
# enabling trust is safe here. No-op when jektex is not loaded.
Jekyll::Hooks.register :site, :after_init do
  next unless defined?(KATEX) && defined?(PATH_TO_JS) && File.readable?(PATH_TO_JS)

  wrapped_source = File.read(PATH_TO_JS) + <<~JS

    ;(function (katex) {
      var renderToString = katex.renderToString;
      katex.renderToString = function (expression, options) {
        options = Object.assign({}, options, { trust: true });
        return renderToString.call(katex, expression, options);
      };
    })(katex);
  JS

  patched = ExecJS.compile(wrapped_source)
  Object.send(:remove_const, :KATEX)
  Object.const_set(:KATEX, patched)
rescue ExecJS::Error, StandardError => e
  Jekyll.logger.warn "[jektex-trust]", "could not enable KaTeX trust mode: #{e.message}"
end
