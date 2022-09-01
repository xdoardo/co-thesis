#!/usr/bin/env python
import json
import re
from random import randrange


def sanitize(s):
    s = s.encode("utf-8").decode("unicode_escape")
    s = re.sub(r"[^\x00-\x7F]+", " ", s)

    conv = {
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\^{}",
        "\\": r"\textbackslash{}",
        "<": r"\textless{}",
        ">": r"\textgreater{}",
        '"': "'",
    }
    regex = re.compile(
        "|".join(
            re.escape(str(key))
            for key in sorted(conv.keys(), key=lambda item: -len(item))
        )
    )
    s = regex.sub(lambda match: conv[match.group()], s)
    return s


def to_bib(cit):
    cit_ref = cit["title"][0:4] + cit["author"][0:4] + str(randrange(129))
    cit_ref = cit_ref.lower()
    cit_ref = "".join(filter(str.isalnum, cit_ref))

    author = cit["author"]
    author = author.replace(";", " and ")
    title = sanitize(cit["title"])
    abstract = re.sub(r"\<.*jats.*\>", "", cit["abstract"])
    abstract = sanitize(abstract)

    return f"""@techreport{{{cit_ref},
    title = "{title}",
    author = "{author}",
    doi = "{cit["doi"]}",
    abstract = "{abstract}"
}}
"""


in_path = "../data/cits.json"
out_path = "../cits.tex"

with open(in_path, "r") as f:
    cits = json.load(f)
    f.close()

bibs = ""

for cit in cits:
    if cit["abstract"] is not None:
        bibs = bibs + to_bib(cit)

latex = rf"""
\RequirePackage{{filecontents}}
\begin{{filecontents}}{{mybib.bib}}
{bibs}
\end{{filecontents}}

\documentclass{{article}}
\usepackage[utf8]{{inputenc}}
\bibliographystyle{{abstract}}
\usepackage[a4paper,margin=1in]{{geometry}}
\usepackage{{url}} % doesn't get used since "abstract" bib style doesn't show contents of 'url' fields
\usepackage[english]{{babel}}

\begin{{document}}
\nocite{{*}}
\bibliography{{mybib}}
\end{{document}}
"""

with open(out_path, "w+") as f:
    f.write(latex)
