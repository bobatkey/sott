;; based on: http://ergoemacs.org/emacs/elisp_syntax_coloring.html

;; define several class of keywords
(setq mykeywords  '("define" "as" "introduce" "use" "for"))
(setq myequality  '("coerce" "refl" "subst"))
(setq myoperators '("->" "=" "/"))
(setq mytypes     '("Set" "Nat"))

;; create the regex string for each class of keywords
(setq mykeywords-regexp  (regexp-opt mykeywords  'words))
(setq myequality-regexp  (regexp-opt myequality 'words))
(setq myoperators-regexp (regexp-opt myoperators))
(setq mytypes-regexp     (regexp-opt mytypes     'words))

;; clear memory
(setq mykeywords  nil)
(setq myequality  nil)
(setq myoperators nil)
(setq mytypes     nil)

;; create the list for font-lock.
;; each class of keyword is given a particular face
(setq myfont-lock-keywords
  `(
    (,mytypes-regexp     . font-lock-type-face)
    (,myequality-regexp  . font-lock-keyword-face)
    (,myoperators-regexp . font-lock-builtin-face)
    (,mykeywords-regexp  . font-lock-keyword-face)
))

;; syntax table
(defvar sott-syntax-table nil "Syntax table for `sott-mode'.")
(setq sott-syntax-table
  (let ((synTable (make-syntax-table)))

  ;; multiple lines
  (modify-syntax-entry ?( ". 1" synTable)
  (modify-syntax-entry ?* ". 23" synTable)
  (modify-syntax-entry ?) ". 4" synTable)

        synTable))

;; define the mode
(define-derived-mode sott-mode fundamental-mode
  "SOTT mode"
  ;; handling comments
  :syntax-table sott-syntax-table
  ;; code for syntax highlighting
  (setq font-lock-defaults '((myfont-lock-keywords)))
  (setq mode-name "sott")
  ;; clear memory
  (setq mykeywords-regexp nil)
  (setq mytypes-regexp nil)
)

(provide 'sott-mode)
