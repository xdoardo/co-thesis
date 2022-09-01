from scrape import Paper
from scrape.find import PaperFinder
from typing import List
from result import Ok, Result
import pandas as pd


class ScopusCSVFinder(PaperFinder):
    path: str

    def __init__(self, path="./data/scopus.csv"):
        self.path = path

    def get_name(self) -> str:
        return "ScopusCSVLoader"

    def get_papers(self, base) -> Result[List[Paper], str]:
        scopus = pd.read_csv(self.path)
        scopus_papers = []
        for _, row in scopus.iterrows():
            author = row["Authors"]
            title = row["Title"]
            doi = row["DOI"]
            abstract = row["Abstract"]
            scopus_papers.append(
                Paper(author=author, title=title, doi=doi, abstract=abstract)
            )
        return Ok(scopus_papers)
