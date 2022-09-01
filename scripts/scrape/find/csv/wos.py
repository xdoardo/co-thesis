from scrape import Paper
from scrape.find import PaperFinder
from typing import List
from result import Ok, Result
import pandas as pd


class WosCSVFinder(PaperFinder):
    path: str

    def __init__(self, path="./data/wos.csv"):
        self.path = path

    def get_name(self) -> str:
        return "WosCSVLoader"

    def get_papers(self, base) -> Result[List[Paper], str]:
        wos = pd.read_csv(self.path)
        wos_papers = []
        for _, row in wos.iterrows():
            author = row["Authors"]
            title = row["Article Title"]
            doi = row["DOI"]
            abstract = row["Abstract"]
            wos_papers.append(
                Paper(author=author, title=title, doi=doi, abstract=abstract)
            )
        return Ok(wos_papers)
