
```
djvups Terese_term_rewriting.djvu  terese.ps
gs -sDEVICE=pdfwrite -dNOPAUSE -dBATCH -sPAPERSIZE=a5 -sOutputFile=final_output_a5.pdf terese.ps
pdftk final_output_a5.pdf cat 2-14 498-907 output terese2.pdf
```
