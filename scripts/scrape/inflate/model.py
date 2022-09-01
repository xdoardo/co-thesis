from abc import ABC, abstractmethod
from typing import List
from scrape import Paper
from result import Result


class Inflator(ABC):
    @abstractmethod
    def get_name(self) -> str:
        pass

    @abstractmethod
    def inflate(self, papers: List[Paper]) -> Result[List[Paper]]:
        del papers
        pass
