;;; host-blog.el --- Host the Jekyll blog in this repository  -*- lexical-binding: t; -*-

;;; Commentary:

;; Provides the `host-blog' command, which runs `bundle exec jekyll
;; serve' in the blog directory and shows the server log in the
;; `*blog-server*' buffer.  Jekyll regenerates the site automatically
;; as files change.  When the server is up, the site URL is opened in
;; a web browser and the window showing the log is closed (the buffer
;; itself remains available for inspection).
;;
;; This library is loaded automatically by .dir-locals.el the first
;; time a file in this repository is visited, so `M-x host-blog' is
;; available only while working on this blog.  Nothing goes in your
;; init file; answer `!' if Emacs asks about the eval form the first
;; time.

;;; Code:

(require 'subr-x)

(defgroup host-blog nil
  "Serve the Jekyll blog in this repository."
  :group 'convenience)

(defcustom host-blog-directory
  (file-name-directory (or load-file-name buffer-file-name default-directory))
  "Root directory of the Jekyll blog."
  :type 'directory
  :group 'host-blog)

(defcustom host-blog-url "http://127.0.0.1:4000/myblog/"
  "URL where `jekyll serve' exposes the blog (baseurl included)."
  :type 'string
  :group 'host-blog)

(defcustom host-blog-buffer "*blog-server*"
  "Buffer showing the output of the Jekyll server process."
  :type 'string
  :group 'host-blog)

(defcustom host-blog-open-browser t
  "When non-nil, open `host-blog-url' once the server is ready."
  :type 'boolean
  :group 'host-blog)

(defcustom host-blog-gem-bin-globs
  '("~/.local/share/gem/ruby/*/bin" "~/.gem/ruby/*/bin")
  "Globs searched for `bundle' when it is not on `exec-path'.
GUI Emacs does not inherit the shell's PATH, so `bundle'
installed with the user gem directory is typically only
reachable through one of these."
  :type '(repeat string)
  :group 'host-blog)

(defun host-blog--gem-bin-dir-with-bundle ()
  "Return the first gem bin directory from `host-blog-gem-bin-globs'
containing a `bundle' executable, or nil."
  (catch 'found
    (dolist (glob host-blog-gem-bin-globs)
      (dolist (dir (file-expand-wildcards glob))
        (when (file-executable-p (expand-file-name "bundle" dir))
          (throw 'found (expand-file-name dir)))))
    nil))

(defun host-blog--find-bundle ()
  "Return (BUNDLE-PROGRAM . BIN-DIR) for running `bundle'.
BUNDLE-PROGRAM is the executable to run and BIN-DIR is the gem
bin directory containing it, or nil when `bundle' is already on
`exec-path'.  Signal an error if it is nowhere to be found."
  (let* ((on-path (executable-find "bundle"))
         (dir (or on-path (host-blog--gem-bin-dir-with-bundle))))
    (unless dir
      (error "host-blog: cannot find `bundle' on `exec-path' or in %s; \
install bundler or customize `host-blog-gem-bin-globs'"
             (mapconcat #'identity host-blog-gem-bin-globs ", ")))
    (if on-path
        (cons on-path nil)
      (cons (expand-file-name "bundle" dir) dir))))

(defun host-blog--live-process ()
  "Return the live Jekyll server process, or nil."
  (let ((buffer (get-buffer host-blog-buffer)))
    (when buffer
      (let ((proc (get-buffer-process buffer)))
        (and (process-live-p proc) proc)))))

(defun host-blog--filter (proc string)
  "Insert PROC output STRING into the server buffer; open site when ready."
  (when (buffer-live-p (process-buffer proc))
    (with-current-buffer (process-buffer proc)
      (let ((follow (= (point) (process-mark proc))))
        (save-excursion
          (goto-char (process-mark proc))
          (insert string)
          (set-marker (process-mark proc) (point)))
        (when follow
          (goto-char (process-mark proc))))
      ;; Jekyll prints e.g. "Server address: http://127.0.0.1:4000/myblog/";
      ;; prefer the URL it reports over `host-blog-url'.
      (when (string-match-p "Server address" string)
        (let ((url (or (and (string-match "Server address: \\(.+\\)" string)
                            (match-string 1 string))
                       host-blog-url)))
          (message "host-blog: serving at %s" url)
          (when host-blog-open-browser
            (browse-url url))
          ;; The server is up: close the window(s) showing this log.
          ;; The buffer stays alive for inspection (it is shown again
          ;; if the server later exits abnormally).
          (quit-windows-on (current-buffer)))))))

(defun host-blog--sentinel (proc event)
  "Report when the Jekyll server PROC exits with EVENT."
  (when (memq (process-status proc) '(signal exit))
    (message "host-blog: server %s" (string-trim event))
    ;; Show the log so the error (e.g. missing `bundle', port in use)
    ;; is visible.
    (when (and (/= 0 (process-exit-status proc))
               (buffer-live-p (process-buffer proc)))
      (display-buffer (process-buffer proc)))))

;;;###autoload
(defun host-blog ()
  "Start hosting the blog with `bundle exec jekyll serve'.

The server log goes to the `*blog-server*' buffer, whose window
closes automatically once the server is ready (the buffer
itself is kept; it is shown again if the server exits
abnormally).  Does nothing if the server is already running.
If `bundle' is not on `exec-path'
(as happens in GUI Emacs, which does not inherit the shell's PATH),
the gem directories in `host-blog-gem-bin-globs' are searched."
  (interactive)
  (if (host-blog--live-process)
      (message "host-blog: already running at %s" host-blog-url)
    (let* ((default-directory host-blog-directory)
           (bundle (host-blog--find-bundle)))
      (with-current-buffer (get-buffer-create host-blog-buffer)
        (let ((inhibit-read-only t))
          (erase-buffer))
        (message "host-blog: starting Jekyll server in %s..."
                 (abbreviate-file-name host-blog-directory))
        ;; Put the gem bin directory on the PATH of Emacs and of the
        ;; server process, so `bundle' and anything it spawns resolve.
        (let* ((bin-dir (cdr bundle))
               (exec-path (if bin-dir (cons bin-dir exec-path) exec-path))
               (process-environment
                (if bin-dir
                    (cons (concat "PATH=" bin-dir path-separator
                                  (getenv "PATH"))
                          process-environment)
                  process-environment))
               (proc (start-process "jekyll-serve" (current-buffer)
                                    (car bundle) "exec" "jekyll" "serve")))
          (set-process-filter proc #'host-blog--filter)
          (set-process-sentinel proc #'host-blog--sentinel)
          (display-buffer (current-buffer)))))))

(provide 'host-blog)
;;; host-blog.el ends here
