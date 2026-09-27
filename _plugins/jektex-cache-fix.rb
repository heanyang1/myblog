# frozen_string_literal: true

# Fix for jektex 0.1.1 wiping Jekyll's disk caches on every build.
#
# jektex's `after_init` hook appends the path of its own cache file to
# `site.config["jektex"]["ignore"]`. Jekyll computes `config.inspect` inside
# `Jekyll::Cache.clear_if_config_changed`, which runs twice per build — once in
# `Site#initialize` (before jektex mutates the config) and once in
# `Site#process` (after). The two fingerprints therefore never match, and
# Jekyll deletes the whole `.jekyll-cache/Jekyll/Cache` tree on every single
# build, forcing kramdown to re-convert every post (~4.5s for this site).
#
# This hook assigns a fresh array back to the config without jektex's runtime
# addition, keeping the fingerprint identical across both checks. jektex's
# internal `$ignored` list still holds the appended pattern (its behaviour is
# unchanged); the pattern was a no-op anyway since it is matched against
# `page.relative_path`, which never starts with ".jekyll-cache/".
Jekyll::Hooks.register :site, :after_init do |site|
  jektex = site.config["jektex"]
  next unless jektex.is_a?(Hash)

  ignore = jektex["ignore"]
  next unless ignore.is_a?(Array)

  jektex["ignore"] = ignore.reject { |entry| entry.to_s.include?("jektex-cache.marshal") }
end
