from scrape.find.model import PaperFinder
from typing import List
from result import Result, Ok, Err
from rich.console import Console
from scrape import Paper
import s2
import requests
import json
from stem import Signal
from stem.control import Controller


class S2Finder(PaperFinder):
    use_tor: bool

    def __init__(self, use_tor=True):
        self.use_tor = use_tor

    def get_name(self) -> str:
        return "SemanticScholar"

    def _get_tor_session(self):
        session = requests.session()
        # Tor uses the 9050 port as the default socks port
        session.proxies = {
            "http": "socks5://127.0.0.1:9050",
            "https": "socks5://127.0.0.1:9050",
        }
        return session

    def _renew_connection(self):
        with Controller.from_port(port=9051) as controller:
            controller.authenticate(password="password")
            controller.signal(Signal.NEWNYM)

    def get_papers(self, base) -> Result[List[Paper], str]:
        try:
            console = Console()
            with console.status(
                "getting ready to scrape SemanticScholar", spinner="earth"
            ) as status:

                status.update("searching paper '" + base.title + "' on SemanticScholar")
                url = (
                    "https://api.semanticscholar.org/graph/v1/paper/search?query="
                    + base.title.replace(" ", "+").replace("-", "+")
                    + "&limit=1"
                )
                if self.use_tor:
                    requests = self._get_tor_session()
                else:
                    import requests

                    requests = requests
                while True:
                    res = requests.get(
                        "https://api.semanticscholar.org/graph/v1/paper/search?query="
                        + base.title.replace(" ", "+").replace("-", "+")
                        + "&limit=1"
                    )

                    if "Too many requests" in res.text:
                        if self.use_tor:
                            status.update(
                                "Got CAPTCHA from S2. Renewing Tor connection..."
                            )
                            self._renew_connection()
                        else:
                            return Err("Got CAPTCHA from S2")
                    else:
                        s2_base = json.loads(res.text)
                        if "data" in s2_base:
                            break

                s2_base = s2_base["data"][0]
                title = s2_base["title"]

                if not title.lower() == base.title.lower():
                    return Err(
                        "Found wrong paper???? '"
                        + title.lower
                        + "' != '"
                        + base.lower()
                        + "'"
                    )

                s2_base = s2.api.get_paper(paperId=s2_base["paperId"])
                if base.doi is None:
                    base.doi = s2_base.doi
                ret = []
                for cit in s2_base.citations:
                    author = cit.authors[0].name
                    doi = cit.doi
                    title = cit.title
                    status.update(
                        "found paper '"
                        + title
                        + "' from author "
                        + author
                        + " doi:"
                        + str(doi)
                    )
                    ret.append(Paper(author=author, doi=doi, title=title))
                return Ok(ret)
        except Exception as e:
            return Err(str(e))
