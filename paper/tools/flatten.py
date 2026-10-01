"""Flatten paper/linnik399.tex into one self-contained .tex: inline every \\input and replace
\\bibliography{...} by the contents of the generated .bbl.  Also scan for code-executing
constructs."""
import re, sys, pathlib
root = pathlib.Path(sys.argv[1])          # paper directory
out = pathlib.Path(sys.argv[2])           # output .tex
main = (root/'linnik399.tex').read_text()
def inline(text):
    def rep(m):
        name = m.group(1)
        p = root/(name if name.endswith('.tex') else name+'.tex')
        body = p.read_text()
        body = re.sub(r'^% !TEX root.*\n', '', body)
        return inline(body)
    return re.sub(r'\\input\{([^}]*)\}', rep, text)
flat = inline(main)
bbl = (root/'linnik399.bbl').read_text()
# Keep \bibliographystyle: amsart also uses it to format bibliography labels.
# The inlined bibliography needs no BibTeX run or external bibliography file.
flat = flat.replace('\\bibliography{references}', bbl.strip())
bad = [r'\\write18', r'\\immediate\\write', r'\\directlua', r'\\luaexec', r'minted', r'pythontex',
       r'\\ShellEscape', r'\\openout', r'\\input\{', r'\\include\{', r'\\usepackage\{shellesc',
       r'\\attachfile', r'\\embedfile', r'filecontents', r'\\special\{']
for b in bad:
    if re.search(b, flat):
        print('FOUND', b)
out.write_text(flat)
print('written', out, len(flat))
