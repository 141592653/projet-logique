;; répertoire des packets
(add-to-list 'load-path "~/.emacs.d")
(require 'package)
(add-to-list 'package-archives '("marmalade" . "https://marmalade-repo.org/packages/"))
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/"))
(add-to-list 'package-archives '("org" . "http://orgmode.org/elpa/") t) ; Org-mode's repository


;; On peut enfin mettre un titre à la fenêtre (avant c'était : "emacs@login",
;; maintenant c'est : "nom_du_fichier (/home/login/..../nom_du_fichier)"
(setq frame-title-format '(buffer-file-name "%b (%f)" "%b"))

;;Undo-tree 
;;(add-to-list 'load-path "~/.emacs.d/elpa/undo-tree-0.6.5")
;;(require 'undo-tree)
;;(global-undo-tree-mode)

;;helm
(add-to-list 'load-path "~/.emacs.d/async")

(add-to-list 'load-path "~/.emacs.d/helm")
(require 'helm-config)
(require 'helm)

;;thème de couleur
(require 'color-theme)
(color-theme-initialize)
(setq color-theme-is-global t)
(color-theme-dark-laptop)

;;suppression barre d'outil et scrolling
(tool-bar-mode -1)
(scroll-bar-mode -1)

;;passer directement en plein écran
(defun toggle-fullscreen ()
(interactive)
(x-send-client-message nil 0 nil "_NET_WM_STATE" 32
'(2 "_NET_WM_STATE_MAXIMIZED_VERT" 0))
(x-send-client-message nil 0 nil "_NET_WM_STATE" 32
'(2 "_NET_WM_STATE_MAXIMIZED_HORZ" 0))
)
(toggle-fullscreen)

;; Afficher les numéros de ligne et colonne
(line-number-mode t)
(column-number-mode t)

;; Pour faire défiler le texte ligne par ligne (sans que le curseur se retrouve
;; au milieu de la page à chaque fois ; on le place 3 lignes avant)
(setq scroll-margin 3)
(setq scroll-step 0)
(setq scroll-conservatively 10)

;;Caml
(setq load-path (cons "~/.emacs.d/tuareg-2.0.9/" load-path))
(setq auto-mode-alist (cons '("\\.ml\\w?" . tuareg-mode) auto-mode-alist))
(autoload 'tuareg-mode "tuareg" "Major mode for editing Caml code" t)
(autoload 'camldebug "camldebug" "Run the Caml debugger" t)

;Python
(load-file "~/.emacs.d/emacs-for-python/epy-init.el")

;;;;Mutlimode php/html;;;
(require 'web-mode)
(add-to-list 'auto-mode-alist '("\\.php5\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.php4\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.php3\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.php\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.html\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.css\\'" . web-mode))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;; C/C++ ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ggtags : navigation dans le code
;; (require 'ggtags)
;; (add-hook 'c-mode-commonhook
;;         (lambda ()
;;          (when (derived-mode-p 'c-mode 'c++-mode 'java-mode 'asm-mode)
;;             (ggtags-mode 1))))


;; (define-key ggtags-mode-map (kbd "C-c g s") 'ggtags-find-other-symbol)
;; (define-key ggtags-mode-map (kbd "C-c g h") 'ggtags-view-tag-history)
;; (define-key ggtags-mode-map (kbd "C-c g r") 'ggtags-find-reference)
;; (define-key ggtags-mode-map (kbd "C-c g f") 'ggtags-find-file)
;; (define-key ggtags-mode-map (kbd "C-c g c") 'ggtags-create-tags)
;; (define-key ggtags-mode-map (kbd "C-c g u") 'ggtags-update-tags)

;; (define-key ggtags-mode-map (kbd "M-,") 'pop-tag-mark)

;;company (code completion)
;; (require 'company)
;; (add-hook 'after-init-hook 'global-company-mode)
;; (add-to-list 'company-backends 'company-c-headers)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;Macros;;;;;;;;;;;;;;;;;;
;;Équivalent du Ctrl-D de notepad++ : copie juste en dessous la lige que l'on est en train d'écrire
(fset 'cpl
   [?\C-a ?\C-  ?\C-e ?\M-w return ?\C-y])
(global-set-key (kbd "C-x t") 'cpl)

;;Fermer la balise html sur la même ligne
(fset 'clhtml
   [?\M-b left ?\C-  ?\M-f right ?\M-w ?\C-y ?\M-b ?/ left left])
(global-set-key (kbd "C-x c") 'clhtml)


;;Fermer la balise html de maière indentée
(fset 'iclhtml
   [?\M-x ?c ?l ?h tab return return return tab up tab])
(global-set-key (kbd "C-x a c") 'iclhtml)

;;Entête html
(fset 'hdhtml
   [?< ?D ?O ?C ?T ?Y ?P ?E ?  ?h ?t ?m ?l ?> ?\C-a right ?! ?\C-e return ?< ?h ?t ?m ?l ?> ?\M-x ?i ?c ?l tab return ?< ?h ?e ?a ?d ?> ?\M-x ?i ?c ?l return ?< ?m ?e ?t ?a ?  ?c ?h ?a ?r ?s ?t ?e backspace backspace ?e ?t ?  ?= ?  ?\" ?u ?t ?f ?- kp-8 ?\" ?/ ?> return tab ?< ?t ?i ?t ?l ?e ?> ?\M-x ?l backspace ?c ?l ?h return end return tab ?< ?l ?i ?n ?k ?  ?r ?e ?l ?  ?= ?  ?\" ?s ?t ?y ?l ?e ?s ?h ?e ?e ?t ?\" ?  ?h ?r ?e ?f ?  ?= ?  ?\" ?. ?c ?s ?s ?\" ?/ ?> ?\C-n return return tab ?< ?b ?o ?d ?y ?> ?\M-x ?i ?c ?l return])

;;Génération d'une ancre
(fset 'genere-ancre
   [?\C-a tab ?\M-f ?\M-f ?\M-f ?\M-b ?\C-  ?\M-f ?\M-w ?\C-e return ?< ?a ?  ?h ?r ?e ?f ?  ?= ?  ?\" ?# ?\C-y ?\" ?> ?\C-p ?\C-a tab ?\M-f ?\M-f ?\M-f ?\M-f ?\M-b ?\C-  ?\C-e ?\M-b ?\M-b ?\M-f ?\M-w ?\C-n ?\C-e ?\C-y ?< ?/ ?\C-  ?\C-a ?\C-w backspace])




(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(inhibit-startup-screen t))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 )
