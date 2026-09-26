# frozen_string_literal: true

# Automatic support for post series.
#
# A post joins a series by setting the `series` key in its front matter:
#
#   ---
#   layout: post
#   title: "Data Flow Analysis with StaPL"
#   series: static-analysis
#   ---
#
# The posts of a series are ordered by date (oldest first).  A post may
# override its position with an explicit `series_order` integer; posts
# without one come after those with one, sorted by date.
#
# For every post in a series this plugin fills in:
#
#   series_part  - 1-based position within the series
#   series_size  - total number of posts in the series
#   series_prev  - the previous post of the series (nil for the first)
#   series_next  - the next post of the series (nil for the last)
#
# and appends " (Part N)" to the post title (unless the series has a
# single post).  These variables are used by the `series_note` include,
# rendered from the `post` layout.  A human-readable description for
# each series lives in `_data/series.yml`.

module Series
  module_function

  def process(site)
    groups = {}
    site.posts.docs.each do |post|
      next unless post.data["series"]

      (groups[post.data["series"].to_s] ||= []) << post
    end

    groups.each_value do |posts|
      posts.sort_by! { |post| [post.data["series_order"] || Float::INFINITY, post.date.to_f, post.path] }
      posts.each_with_index do |post, index|
        part = index + 1
        post.data["series_part"] = part
        post.data["series_size"] = posts.size
        post.data["series_prev"] = index.positive? ? posts[index - 1] : nil
        post.data["series_next"] = index < posts.size - 1 ? posts[index + 1] : nil
        next unless posts.size > 1

        post.data["title"] = "#{post.data['title']} (Part #{part})"
      end
    end
  end
end

Jekyll::Hooks.register :site, :post_read do |site|
  Series.process(site)
end
