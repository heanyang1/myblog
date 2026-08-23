# My Blog

A very simple blog that uses Jekyll with the most basic configuration.

## Plugins Added

- [jektex](https://github.com/yagarea/jektex) for rendering math.
- [jekyll-diagrams](https://github.com/zhustec/jekyll-diagrams) for rendering Graphviz diagrams.

## Run locally

1. [Install Jekyll](https://jekyllrb.com/docs/installation/) and [Graphviz](https://graphviz.org/)
2. On Arch Linux, you may need to add `~/.local/share/gem/ruby/[version]/bin` to `$PATH` to run `bundle`.
3. `bundle install && bundle exec jekyll serve`

In Emacs, `M-x host-blog` runs `jekyll serve` in a `*blog-server*` buffer and opens the site in your browser once ready. The script is LLM-generated.