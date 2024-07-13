from scipy import weave

code = 'printf("Hello Weave");'
weave.inline(code)
