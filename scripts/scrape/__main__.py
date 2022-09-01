import logging
import os.path

from fake_useragent.utils import json
from scrape import Paper
from scrape.find import ScholarFinder, S2Finder
from scrape.find.csv import WosCSVFinder, ScopusCSVFinder
from scrape.filter import UniqFilter
from result import Ok

logging.basicConfig()

# Uncomment to clutter your screen
# logging.getLogger().setLevel(logging.INFO)

base = Paper(
    author="Xavier Leroy",
    title="Coinductive big-step operational semantics",
)

dump_path = "cits.json"
finders = [
    # Uncomment to scrape GoogleScholar
    # ScholarFinder(),
    # Uncomment to scrape SemanticScholar
    # S2Finder(),
    WosCSVFinder(),
    ScopusCSVFinder(),
]
filters = [UniqFilter()]

papers = [base]
if os.path.exists(dump_path):
    with open(dump_path, "r+") as f:
        papers_json = json.load(f)
        for p in papers_json:
            abstract = p["abstract"]
            if abstract is not None:
                abstract = abstract.encode().decode("unicode-escape")
            papers.append(
                Paper(
                    author=p["author"],
                    title=p["title"],
                    doi=p["doi"],
                    abstract=abstract,
                )
            )
if len(papers) != 0:
    print("loaded ", len(papers), " papers")

for finder in finders:
    res = finder.get_papers(base)
    if isinstance(res, Ok):
        res = res.ok()
        papers = papers + res
        print("from finder", finder.get_name(), "got", len(res), "papers")
    else:
        print("from finder", finder.get_name(), "", res)

print("without DOI:", len(list(filter(lambda x: x.doi is None, papers))))
print("without abstract:", len(list(filter(lambda x: x.abstract is None, papers))))

for filt in filters:
    res = filt.filter(papers)
    if isinstance(res, Ok):
        papers = res.ok()
        print(
            "after filter",
            filt.get_name(),
            "without DOI:",
            len(list(filter(lambda x: x.doi is None, papers))),
        )
        print(
            "after filter",
            filt.get_name(),
            "without abstract:",
            len(list(filter(lambda x: x.abstract is None, papers))),
        )

    else:
        print("from filter", filt.get_name(), ":", res)


print("writing", len(papers), "papers")

with open(dump_path, "w+") as f:
    json.dump([p.__dict__ for p in papers], f, indent=4, sort_keys=True)
