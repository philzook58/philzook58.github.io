---
author: philzook58
comments: true
date: 2019-07-28 21:11:28+00:00
layout: post
link: https://www.philipzucker.com/?p=784
published: false
slug: Common Lisp
title: Common Lisp
wordpress_id: 784
---




I install quicklisp using these instructions







[https://www.quicklisp.org/beta/#installation](https://www.quicklisp.org/beta/#installation)







sbcl --load quicklisp.lisp 







basically







M-x slime starts up slime








https://www.youtube.com/watch?v=SPgjgybGb5o








quickproject to make a project template







a playlist of getting started








https://www.youtube.com/playlist?list=PL2VAYZE_4wRIoHsU5cEBIxCYcbHzy4Ypj








[https://common-lisp.net/project/asdf/](https://common-lisp.net/project/asdf/)







asdf is something like make.  It is commonly used








http://lisp-univ-etc.blogspot.com/2019/07/programming-algorithms-book.html








[https://nikodemus.github.io/screamer/](https://nikodemus.github.io/screamer/) nondeterminstic computation (logic programming)







[https://github.com/guicho271828/trivia](https://github.com/guicho271828/trivia) (pattern matching)







[http://stevelosh.com/blog/2018/08/a-road-to-common-lisp/](http://stevelosh.com/blog/2018/08/a-road-to-common-lisp/)







[https://github.com/vydd/sketch](https://github.com/vydd/sketch) digital art in common lisp. like Processing sketches







[http://www.lispworks.com/documentation/lw70/CLHS/Front/index.htm](http://www.lispworks.com/documentation/lw70/CLHS/Front/index.htm) the hyperspec







[https://github.com/CodyReichert/awesome-cl](https://github.com/CodyReichert/awesome-cl)







[https://lispcookbook.github.io/cl-cookbook/](https://lispcookbook.github.io/cl-cookbook/)







[https://common-lisp.net/project/alexandria/draft/alexandria.html#Top](https://common-lisp.net/project/alexandria/draft/alexandria.html#Top)











    
    brew install sbcl




 




 




https://www.youtube.com/watch?v=VnWVu8VVDbI




 




I've heard good things. That somehow it is superior and more realworld than scheme and racket.




SBCL is the most commonly used compiler.




Quicklisp as a package manager?




Two book people reccommend are Practical Common Lisp and A Gentle Introduction to Symbolic Computation




This is extremely useful. It actually has up to date ish info on useful packages




http://lispcookbook.github.io/cl-cookbook/




 




 




And there are some really neat topics in Norvig's older book Common Lisp AI stuff. Especially interested in the Macsyma chapter.




Compiled rather than interpreted. Supposedly possible to be pretty quick running. (Everybody tries to say this though. TBD if true)




some emacs stuff:




C-c C-x to quit




C-x C-s to save




C-x C-f for new file




C-x C-b for buffer stuff




C-y to paste




M-w to copy




God I hate that emacs has its own dumb copy and paste hotkeys. I also feel bad about changing it.




Supposedly the coding interaction is somehow different from everyone. https://github.com/slime/slime. Atom-slime also exists but is not recommended?




to start slime



    
    M-x slime




Where M is the meta key. Alt on my computer works. Sometimes escape works.




C-c C-k compiles and loads whole file




C-c C-c compiles just current function?




C-x C-e evaluates a line




This is pretty nice. I kind of see what they mean about incrementally changing your program.




A cheat sheet. There is also stuff in the toolbar, although it isn't obvious what the important ones are




http://pchristensen.com/wp-content/uploads/2008/02/slimecommands.pdf




I also like the tooltips at the bottom. I suppose if I ever used actual IDEs rather than text editors I'd be used to that.




 




defparameter for global variables




defun for function declaration




lambda for anaonymous functions




setf to change value




make-array for arrays. Give a dimensions list, can be given adjustable parameter




aref for array indexing




map is mapcar?




hmmm mapcar is overloaded to zip map also / be applicative




filter is remove-if-not




That is annoying.




 




Roswell as an installer?




https://blog.teknik.io/phoe/p/365




People were shitting on cl21 but it seems interesting https://github.com/cl21/cl21




Vecto - vector graphics library




[https://www.xach.com/lisp/vecto/](https://www.xach.com/lisp/vecto/)




Lisp Hackers Testimony




https://leanpub.com/lisphackers/read




 
