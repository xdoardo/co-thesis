from abc import ABC, abstractmethod
from typing import List
from scrape import Paper
from result import Result


class Filter(ABC):
    @abstractmethod
    def get_name(self) -> str:
        pass

    @abstractmethod
    def filter(self, papers: List[Paper]) -> Result[List[Paper], str]:
        del papers
        pass
