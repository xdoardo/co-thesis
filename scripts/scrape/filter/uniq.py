from typing_extensions import DefaultDict
from scrape.filter.model import Filter
from typing import List
from scrape import Paper
from result import Result, Ok


class UniqFilter(Filter):
    def get_name(self) -> str:
        return "Uniq"

    def _score_paper(self, paper: Paper) -> int:
        score = 0
        if paper.title is not None:
            score = score + 1
        if paper.author is not None:
            score = score + 1
        if paper.abstract is not None:
            score = score + 3
        if paper.doi is not None:
            score = score + 3

        return 0

    def filter(self, papers: List[Paper]) -> Result[List[Paper], str]:

        index_paper_dict = dict([(i, p) for i, p in enumerate(papers)])
        title_indices_dict = DefaultDict(lambda: [])

        for index, paper in index_paper_dict.items():
            title_indices_dict[paper.title.lower()].append(index)

        papers = []

        for indices in title_indices_dict.values():
            papers.append(
                max([index_paper_dict[i] for i in indices], key=self._score_paper)
            )
        return Ok(papers)
