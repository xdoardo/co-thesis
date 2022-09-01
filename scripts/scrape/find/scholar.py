from scrape.find.model import PaperFinder
from typing import List
from result import Result, Ok, Err
from scholarly import scholarly
from scholarly import ProxyGenerator
from rich.console import Console
from scrape import Paper

import stem
import logging

stem.util.log.get_logger().setLevel(logging.NOTSET)


class ScholarFinder(PaperFinder):
    use_tor: bool
    external: bool
    tor_cmd: str

    def __init__(self, use_tor=True, external=False, tor_cmd="tor"):
        self.use_tor = use_tor
        self.tor_cmd = tor_cmd
        self.external = external

    def get_name(self) -> str:
        return "GoogleScholar"

    def get_papers(self, base) -> Result[List[Paper], str]:
        try:
            pg = ProxyGenerator()
            console = Console()
            with console.status(
                "getting ready to scrape GScholar...", spinner="earth"
            ) as status:
                if self.use_tor:
                    try:
                        status.update(
                            "trying to start tor with command '" + self.tor_cmd + "'"
                        )
                        if self.external:
                            pg.Tor_External(
                                tor_sock_port=9050,
                                tor_control_port=9051,
                                tor_password="",
                            )
                        else:
                            pg.Tor_Internal(tor_cmd=self.tor_cmd)
                    except BaseException as e:
                        return Err(str(e))
                scholarly.use_proxy(pg)

                status.update("searching paper '" + base.title + "' on GScholar..")
                while True:
                    try:
                        gs_base = scholarly.search_single_pub(base.title)
                        break
                    except Exception:
                        continue

                title = gs_base["bib"]["title"]
                author = gs_base["bib"]["author"][0]

                if not title.lower() == base.title.lower():
                    return Err(
                        "Found wrong paper???? '"
                        + title.lower
                        + "' != '"
                        + base.lower()
                        + "'"
                    )

                ret = []
                for cit in scholarly.citedby(gs_base):
                    title = cit["bib"]["title"]
                    author = cit["bib"]["author"][0]
                    status.update("found paper '" + title + "' from author " + author)
                    ret.append(Paper(author=author, title=title))
                return Ok(ret)
        except Exception as e:
            print(e)
            return Err(str(e))
