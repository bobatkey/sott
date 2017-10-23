;; based on: http://ergoemacs.org/emacs/elisp_syntax_coloring.html

;; define several class of keywords
(setq sott-keywords  '("define" "as" "introduce" "use" "for"))
(setq sott-equality  '("coerce" "refl" "subst"))
(setq sott-operators '("->" "=" "/"))
(setq sott-types     '("Set" "Nat"))

;; create the regex string for each class of keywords
(setq sott-keywords-regexp  (regexp-opt sott-keywords  'words))
(setq sott-equality-regexp  (regexp-opt sott-equality 'words))
(setq sott-operators-regexp (regexp-opt sott-operators))
(setq sott-types-regexp     (regexp-opt sott-types     'words))

;; clear memory
(setq sott-keywords  nil)
(setq sott-equality  nil)
(setq sott-operators nil)
(setq sott-types     nil)

;; create the list for font-lock.
;; each class of keyword is given a particular face
(setq sott-font-lock-keywords
  `(
    (,sott-types-regexp     . font-lock-type-face)
    (,sott-equality-regexp  . font-lock-keyword-face)
    (,sott-operators-regexp . font-lock-builtin-face)
    (,sott-keywords-regexp  . font-lock-keyword-face)
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
  (setq font-lock-defaults '((sott-font-lock-keywords)))
  (setq mode-name "sott")
  ;; clear memory
  (setq sott-keywords-regexp nil)
  (setq sott-types-regexp nil)
)

(provide 'sott-mode)
