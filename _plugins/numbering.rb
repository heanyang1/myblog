# frozen_string_literal: true

require "strscan"

# Automatic numbering for labeled theorems and equations, and hyperlinks
# from every reference to its label.
#
# Posts opt in by writing LaTeX-ish markers instead of hardcoded numbers:
#
#   **Lemma.**\label{lem:compose-monotone} Let ...
#     =>  <a id="lem:compose-monotone"></a>**Lemma 3.** Let ...
#   **Proposition**\label{prop:right-adjoint-product} (title). ...
#     =>  <a id="prop:right-adjoint-product"></a>**Proposition 4** (title). ...
#   \[ e = mc^2 \tag{eq:mass-energy} \]
#     =>  <a id="eq:mass-energy"></a>\[ e = mc^2 \tag{7} \]
#
# and reference them from anywhere (prose, code comments, even inside math):
#
#   \ref{lem:compose-monotone}  =>  Lemma 3    (in prose: a link to the lemma)
#   \eqref{eq:mass-energy}      =>  (7)        (in prose: a link to the equation)
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
#   (the surrounding prose supplies the context, e.g. "... in Part 2");
#   such references link to `post-url#key` instead of just `#key`.
# * Duplicate keys and unresolved references are reported as build warnings.
#
# Every resolved reference becomes a hyperlink to its label, in every
# context that can carry one:
#
# * prose: the reference text becomes `<a class="ref" href="#key">...</a>`
#   and the label gets an empty anchor `<a id="key"></a>` right before it,
#   so that `#key` resolves on the page (a ":" is legal in HTML ids).
# * inside math (`\(...\)` / `\[...\]`): the reference becomes a KaTeX
#   `\href{#key}{...}` and the display equation carrying a managed `\tag`
#   gets the same `<a id="key"></a>` anchor in front of it. KaTeX only
#   honours `\href` in trust mode, which _plugins/jektex-trust.rb turns on.
# * inside code (fences, `{% highlight %}` blocks, inline code spans): the
#   reference is still replaced by its plain text --- a link there would
#   surface as literal markup.
#
# Everything happens in a :post_read site hook, before jektex and kramdown
# see the content, so the numbers, anchors and links end up in the KaTeX
# source and the rendered HTML exactly as if they had been written by hand.

module Numbering
  # **Lemma.**\label{key} or **Proposition**\label{key}
  DECLARATION_RE = /\*\*([A-Z][A-Za-z]*)(\.)?\*\*\\label\{([^{}\s]+)\}/.freeze
  # \tag{key} --- only keys containing ":" are managed
  TAG_RE = /\\tag\{([^{}\s]*:[^{}\s]*)\}/.freeze
  # \ref{key} or \eqref{key}
  REF_RE = /\\(eqref|ref)\{([^{}\s]+)\}/.freeze

  # Where prose ends and another context begins. Order matters: the
  # line-anchored fence must precede the bare backtick run, or ``` would
  # open a code span instead of a code block.
  SPECIAL_RE = /\\\[|\\\(|{%\s*(?:highlight|raw)\b|^ {0,3}(?:`{3,}|~{3,})[^\n]*(?:\n|\z)|`+/.freeze
  # {% highlight lang %} or {% raw %}, matched against the start of a token
  HIGHLIGHT_RE = /\A{%\s*(highlight|raw)\b/.freeze

  # A resolved label. `kind` is "equation" for \tag labels; `url` is the
  # hosting post's URL (without the baseurl).
  Label = Struct.new(:kind, :number, :path, :url)

  module_function

  def process(site)
    registry = {}
    counters = Hash.new(0)
    baseurl = site.config["baseurl"].to_s.chomp("/")

    # Pass 1: number every declaration of every post, in reading order.
    # Cross-post references work because no content is rewritten yet.
    site.posts.docs.each do |post|
      url = post.url
      post.content.scan(DECLARATION_RE) { |kind, _dot, key| register(registry, counters, post, key, kind, url) }
      post.content.scan(TAG_RE) { |(key)| register(registry, counters, post, key, "equation", url) }
    end

    # Pass 2: rewrite declarations, tags and references, adding anchors at
    # the labels and links at the references.
    site.posts.docs.each { |post| rewrite(post, registry, baseurl) }
  end

  def register(registry, counters, post, key, kind, url)
    number = counters[[post.path, kind]] += 1
    if registry.key?(key)
      Jekyll.logger.warn "[numbering]", "duplicate label #{key} in #{post.path} " \
                                        "(kept the one in #{registry[key].path})"
    else
      registry[key] = Label.new(kind, number, post.path, url)
    end
  end

  def rewrite(post, registry, baseurl)
    post.content = segment(post.content).map do |mode, text|
      case mode
      when :prose then rewrite_prose(text, post, registry, baseurl)
      when :math  then rewrite_math(text, post, registry, baseurl)
      else             rewrite_code(text, post, registry, baseurl)
      end
    end.join
  end

  # Splits content into :prose, :math and :code segments so that references
  # can be replaced appropriately per context. The math delimiters mirror
  # jektex's own regexes, so both agree on where every expression ends.
  def segment(content)
    segments = []
    ss = StringScanner.new(content)
    until ss.eos?
      consumed = ss.scan_until(SPECIAL_RE)
      if consumed.nil?
        segments << [:prose, ss.rest] unless ss.rest.empty?
        break
      end
      token = ss.matched
      pre = consumed[0, consumed.length - token.length]
      segments << [:prose, pre] unless pre.empty?
      ss.pos -= token.length # rewind to the start of the token
      segments << consume_special(ss, token)
    end
    segments
  end

  def consume_special(ss, token)
    if token.start_with?("\\(")
      [:math, ss.scan(/\\\((?m:.*?)(?<!\\)\\\)/) || rest_of(ss)]
    elsif token.start_with?("\\[")
      [:math, ss.scan(/\\\[(?m:.*?)(?<!\\)\\\]/) || rest_of(ss)]
    elsif (kind = token[HIGHLIGHT_RE, 1])
      closed = ss.scan(/(?m:.*?\{%\s*end#{kind}\s*%\})/)
      [:code, closed || rest_of(ss)]
    elsif token.include?("\n") # opening fence line
      marker = token[/[`~]{3,}/][0]
      ss.pos += token.length # step over the opener line
      closed = ss.scan(/(?m:.*?^ {0,3}#{marker}{3,}[ \t]*(?:\n|\z))/)
      [:code, token + (closed || rest_of(ss))]
    else # inline code span of token.length backticks
      ss.pos += token.length # step over the opener
      closed = ss.scan(/(?m:.*?`{#{token.length},}(?!`))/)
      [:code, token + (closed || rest_of(ss))]
    end
  end

  def rest_of(ss)
    ss.scan(/(?m:.*\z)/) || ""
  end

  def rewrite_prose(prose, post, registry, baseurl)
    prose = prose.gsub(DECLARATION_RE) { replace_declaration(Regexp.last_match, registry) }
    prose.gsub(REF_RE) { replace_ref(post, Regexp.last_match, registry, :prose, baseurl) }
  end

  def rewrite_math(math, post, registry, baseurl)
    anchor_key = nil
    math = math.gsub(TAG_RE) do
      key = Regexp.last_match(1)
      anchor_key ||= key if registry.key?(key)
      "\\tag{#{registry[key].number}}"
    end
    math = math.gsub(REF_RE) { replace_ref(post, Regexp.last_match, registry, :math, baseurl) }
    math = %(<a id="#{anchor_key}"></a>) + math if anchor_key
    math
  end

  def rewrite_code(code, post, registry, baseurl)
    code.gsub(REF_RE) { replace_ref(post, Regexp.last_match, registry, :plain, baseurl) }
  end

  # Each gsub block passes Regexp.last_match explicitly because $~ is
  # frame-local: it is nil inside a method called from the block.
  def replace_declaration(match, registry)
    kind = match[1]
    dot = match[2] || ""
    number = registry[match[3]].number
    %(<a id="#{match[3]}"></a>) + "**#{kind} #{number}#{dot}**"
  end

  def replace_ref(post, match, registry, mode, baseurl)
    key = match[2]
    label = registry[key]
    if label.nil?
      Jekyll.logger.warn "[numbering]", "unknown label #{key} referenced in #{post.path}"
      return match[0]
    end
    text = label.kind == "equation" ? "(#{label.number})" : "#{label.kind} #{label.number}"
    target = label.url == post.url ? "##{key}" : "#{baseurl}#{label.url}##{key}"
    case mode
    when :prose
      %(<a class="ref" href="#{target}">#{text}</a>)
    when :math
      body = label.kind == "equation" ? text : "\\text{#{text}}"
      "\\href{#{target}}{#{body}}"
    else
      text
    end
  end
end

Jekyll::Hooks.register :site, :post_read do |site|
  Numbering.process(site)
end
