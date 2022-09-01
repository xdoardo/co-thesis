from typing import Optional


class Paper:
    author: str
    title: str
    doi: Optional[str]
    abstract: Optional[str]

    def __init__(
        self,
        author: str,
        title: str,
        doi: Optional[str] = None,
        abstract: Optional[str] = None,
    ):
        self.author = author
        self.title = title
        self.doi = doi
        self.abstract = abstract
