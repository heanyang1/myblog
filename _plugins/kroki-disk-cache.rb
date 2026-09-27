# frozen_string_literal: true

# Persist jekyll-kroki's rendered diagrams across builds.
#
# jekyll-kroki keeps rendered SVGs only in an in-memory cache
# (`Jekyll::Kroki.diagram_cache`), so every build re-uploads all diagram
# sources to kroki.io and waits for the network round-trip. This plugin saves
# that cache to disk after each build and restores it before rendering, which
# removes the network from warm builds entirely. Diagrams that are new or
# edited are still fetched (the cache key is the SHA1 of the diagram source).
require "fileutils"

module KrokiDiskCache
  PATH = File.join(".jekyll-cache", "kroki-cache.marshal")

  module_function

  def restore
    return unless File.exist?(PATH)

    saved = Marshal.load(File.binread(PATH)) # rubocop:disable Security/MarshalLoad
    cache = Jekyll::Kroki.instance_variable_get(:@diagram_cache)
    return unless cache.is_a?(Concurrent::Map) && saved.is_a?(Hash)

    saved.each { |key, svg| cache.put_if_absent(key, svg) }
    Jekyll.logger.info "[kroki-disk-cache] Restored #{saved.size} rendered diagrams"
  rescue StandardError => e
    Jekyll.logger.warn "[kroki-disk-cache] Could not restore cache: #{e.message}"
  end

  def save
    cache = Jekyll::Kroki.instance_variable_get(:@diagram_cache)
    return unless cache.is_a?(Concurrent::Map) && !cache.empty?

    FileUtils.mkdir_p(File.dirname(PATH))
    tmp = "#{PATH}.tmp"
    File.binwrite(tmp, Marshal.dump(cache.each_pair.to_h))
    File.rename(tmp, PATH)
  rescue StandardError => e
    Jekyll.logger.warn "[kroki-disk-cache] Could not save cache: #{e.message}"
  end
end

Jekyll::Hooks.register :site, :after_init do |_site|
  KrokiDiskCache.restore
end

Jekyll::Hooks.register :site, :post_write do
  KrokiDiskCache.save
end
