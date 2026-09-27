# frozen_string_literal: true

# Automatic numbering for labeled theorems and equations.
#
# Posts opt in by writing LaTeX-ish markers instead of hardcoded numbers:
#
#   **Lemma.**\label{lem:compose-monotone} Let ...
#     =>  **Lemma 3.** Let ...
#   **Proposition**\label{prop:right-adjoint-product} (title). ...
#     =>  **Proposition 4** (title). ...
#   \[ e = mc^2 \tag{eq:mass-energy} \]
#     =>  \[ e = mc^2 \tag{7} \]
#
# and reference them from anywhere (prose, code comments, even inside math):
#
#   \ref{lem:compose-monotone}  =>  Lemma 3
#   \eqref{eq:mass-energy}      =>  (7)
#   \ref{eq:mass-energy}        =>  (7)
#
# Rules:
# * Theorem-like counters are per post and per kind (the capitalized word in
#   bold); equations share one counter per post. Kinds are not restricted ---
#   Definition, Theorem, Lemma, Proposition, Example, Corollary, ... all work.
# * A trailing period inside the bold (`**Lemma.**`) is kept in the output
#   (`**Lemma 3.**`); punctuation after the label is up to the writer.
# * A `\tag{...}` is managed iff its argument contains a colon, so fixed
#   symbolic tags like `T-Num` are left untouched.
# * Label keys are global across the blog, so cross-post references work
#   (the surrounding prose supplies the context, e.g. "... in Part 2").
# * Duplicate keys and unresolved references are reported as build warnings.
#
# Everything happens in a :post_read site hook, before jektex and kramdown
# see the content, so the numbers end up in the KaTeX source and the rendered
# HTML exactly as if they had been written by hand.

module Numbering
  # **Lemma.**\label{key} or **Proposition**\label{key}
  DECLARATION_RE = /\*\*([A-Z][A-Za-z]*)(\.)?\*\*\\label\{([^{}\s]+)\}/.freeze
  # \tag{key} --- only keys containing ":" are managed
  TAG_RE = /\\tag\{([^{}\s]*:[^{}\s]*)\}/.freeze
  # \ref{key} or \eqref{key}
  REF_RE = /\\(eqref|ref)\{([^{}\s]+)\}/.freeze

  # A resolved label. `kind` is "equation" for \tag labels.
  Label = Struct.new(:kind, :number, :path)

  module_function

  def process(site)
    registry = {}
    counters = Hash.new(0)

    # Pass 1: number every declaration of every post, in reading order.
    # Cross-post references work because no content is rewritten yet.
    site.posts.docs.each do |post|
      post.content.scan(DECLARATION_RE) do |kind, _dot, key|
        register(registry, counters, post, key, kind)
      end
      post.content.scan(TAG_RE) do |(key)|
        register(registry, counters, post, key, "equation")
      end
    end

    # Pass 2: rewrite declarations and references.
    site.posts.docs.each { |post| rewrite(post, registry) }
  end

  def register(registry, counters, post, key, kind)
    number = counters[[post.path, kind]] += 1
    if registry.key?(key)
      Jekyll.logger.warn "[numbering]", "duplicate label #{key} in #{post.path} " \
                                        "(kept the one in #{registry[key].path})"
    else
      registry[key] = Label.new(kind, number, post.path)
    end
  end

  def rewrite(post, registry)
    post.content = post.content
                            .gsub(DECLARATION_RE) { replace_declaration(Regexp.last_match, registry) }
                            .gsub(TAG_RE) { replace_tag(Regexp.last_match, registry) }
                            .gsub(REF_RE) { replace_ref(post, Regexp.last_match, registry) }
  end

  # Each gsub block passes Regexp.last_match explicitly because $~ is
  # frame-local: it is nil inside a method called from the block.
  def replace_declaration(match, registry)
    kind = match[1]
    dot = match[2] || ""
    number = registry[match[3]].number
    "**#{kind} #{number}#{dot}**"
  end

  def replace_tag(match, registry)
    "\\tag{#{registry[match[1]].number}}"
  end

  def replace_ref(post, match, registry)
    label = registry[match[2]]
    if label.nil?
      Jekyll.logger.warn "[numbering]", "unknown label #{match[2]} referenced in #{post.path}"
      match[0]
    elsif label.kind == "equation"
      "(#{label.number})"
    else
      "#{label.kind} #{label.number}"
    end
  end
end

Jekyll::Hooks.register :site, :post_read do |site|
  Numbering.process(site)
end
