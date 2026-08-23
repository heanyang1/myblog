;;; .dir-locals.el --- Local variables for the blog  -*- lexical-binding: t; -*-

;; Load the `host-blog' command (M-x host-blog) the first time a file
;; in this repository is visited.  Emacs will ask whether to run the
;; eval form the first time; answer `!' to remember the choice.

((nil . ((eval . (unless (featurep 'host-blog)
                   (load (expand-file-name
                          "host-blog.el"
                          (locate-dominating-file default-directory ".dir-locals.el"))
                         nil t))))))
