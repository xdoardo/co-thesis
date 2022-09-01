from abc import ABC, abstractmethod
from typing import List
from result import Result
from scrape import Paper


class PaperFinder(ABC):

    @abstractmethod 
    def get_name(self) -> str:
        pass

    @abstractmethod
    def get_papers(self, base) -> Result[List[Paper], str]:
        pass
