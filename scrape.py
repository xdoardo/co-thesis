#!/usr/bin/env python
# coding: utf-8


from typing import Optional
import json
import logging

logging.basicConfig()
# Change to different level to suppress messages...
logging.getLogger().setLevel(logging.INFO)


class Article:
    author: str
    title: str
    doi: Optional[str]
    abstract: Optional[str]
    publisher: Optional[str]

    def __init__(
        self,
        author: str,
        title: str,
        doi: Optional[str] = None,
        abstract: Optional[str] = None,
        publisher: Optional[str] = None,
    ):
        self.author = author
        self.title = title
        self.doi = doi
        self.abstract = abstract
        self.publisher = publisher


base = Article(
    author="Xavier Leroy",
    title="Coinductive big-step operational semantics",
)

# Set this to True to redo the scraping.
scrape = False

# Scrape Google Scholar
do_gs = True
# Scrape SemanticScholar
do_s2 = True


cits = {}

if not scrape:
    try:
        with open("citations.json") as f:
            articles = json.load(f)
            for article in articles:
                cits[article["title"]] = Article(
                    author=article["author"],
                    title=article["title"],
                    doi=article["doi"],
                    abstract=article["abstract"],
                )
    except BaseException:
        raise
else:

    # This will take a lot of time.
    if do_gs:
        # google scholar scraper
        from scholarly import scholarly

        # Avoid Google CAPTCHAs...
        from scholarly import ProxyGenerator

        pg = ProxyGenerator()

        use_tor = True
        if use_tor:
            success = pg.Tor_Internal(tor_cmd="tor")
            if not success:
                print("Tor not working...")
                raise
        else:
            pg.FreeProxies()
            import ssl

            ssl._create_default_https_context = ssl._create_unverified_context

        scholarly.use_proxy(pg)

        gs_base = scholarly.search_single_pub(base.title)
        logging.info(
            "fetched gscholar pub for base article " +
            str(base) +
            " : " +
            str(gs_base))
        assert gs_base["bib"]["title"] == base.title

        gs_cits = []
        for cit in scholarly.citedby(gs_base):
            logging.info(
                "citation "
                + str(cit["bib"]["author"][0])
                + " "
                + cit["bib"]["title"]
                + " cited base"
            )
            gs_cits.append(cit)

        for cit in gs_cits:
            author, title = cit["bib"]["author"][0], cit["bib"]["title"]
            cits[title] = Article(author=author, title=title)

    if do_s2:
        import s2
        import requests

        res = requests.get(
            "https://api.semanticscholar.org/graph/v1/paper/search?query="
            + base.title.replace(" ", "+").replace("-", "+")
            + "&limit=1"
        )
        s2_base = json.loads(res.text)
        logging.info(
            "fetched s2 pub for base article " +
            str(base) +
            " : " +
            str(s2_base))
        s2_base = s2_base["data"][0]
        assert s2_base["title"] == base.title
        s2_base = s2.api.get_paper(paperId=s2_base["paperId"])
        base.doi = s2_base.doi
        for cit in s2_base.citations:
            author, doi, title = (
                cit.authors[0].name,
                cit.doi,
                cit.title,
            )
            logging.info(
                "cit " +
                str(author) +
                " " +
                str(title) +
                " cited base")
            cits[title] = Article(author=author, doi=doi, title=title)

    with open("citations.json", "w+") as f:
        to_write = [cit.__dict__ for cit in cits.values()]
        json.dump(to_write, f)
    # Try to fill each article.

# Set this to True to (try to) fill the scraped articles with DOI and abstract.
fill = True

if fill:
    # crossref.org client
    import habanero

    cr = habanero.Crossref()

    user_mail = "ecmm@anche.no"
    habanero.Crossref(mailto=user_mail)
    from tqdm import tqdm
    from tqdm.contrib.logging import logging_redirect_tqdm

    with logging_redirect_tqdm():
        for cit in tqdm(cits.values()):

            if cit.doi is None or cit.abstract is None or cit.publisher is None:

                logging.info("filling cit " + str(cit.__dict__))
                do_extsearch = True
                if cit.doi is not None:
                    logging.info("cit has doi: " + cit.doi)
                    try:
                        res = cr.works(ids=cit.doi)
                        if not res["status"] == "ok":
                            # raise Exception("Error fetching crossref work for citation " + str(cit))
                            logging.error(
                                "Error fetching crossref work for citation " + str(cit))
                            continue
                        item = res["message"]
                        # logging.info("message: " + str(item))
                        abstract = None
                        if "abstract" in item:
                            abstract = item["abstract"]
                        publisher = None
                        if "publisher" in item:
                            publisher = item["publisher"]
                        if cit.abstract is None:
                            cit.abstract = cit.abstract
                        if cit.publisher is None:
                            cit.publisher = cit.publisher
                        logging.info("update cit from doi: " +
                                     str(cit.__dict__))
                        do_extsearch = False
                    except BaseException as e:
                        logging.error(str(e))
                        cit.doi = None
                        pass

                if do_extsearch:
                    logging.info("cit does not have doi: " + cit.title)
                    res = cr.works(
                        query=cit.title,
                        select=[
                            "DOI",
                            "title",
                            "author",
                            "abstract",
                            "publisher"],
                    )

                    res1 = cr.works(
                        query=cit.title +
                        " " +
                        cit.author,
                        query_author=cit.author,
                        select=[
                            "DOI",
                            "title",
                            "author",
                            "abstract",
                            "publisher"],
                    )

                    res2 = cr.works(
                        query_title=cit.title,
                        select=[
                            "DOI",
                            "title",
                            "author",
                            "abstract",
                            "publisher"],
                    )

                    res3 = cr.works(
                        query_container_title=cit.title,
                        select=[
                            "DOI",
                            "title",
                            "author",
                            "abstract",
                            "publisher"],
                    )

                    items = res["message"]["items"] + res1["message"]["items"] + \
                        res2["message"]["items"] + res3["message"]["items"]

                    logging.info("checking " + str(len(items)) + " candidates")
                    # logging.info(str(res))
                    for item in items:
                        #logging.info("trying item " + item)
                        try:
                            title = item["title"][0]
                            if not title.lower() == cit.title.lower():
                                continue
                            if "DOI" not in item:
                                continue
                            doi = item["DOI"]
                            abstract = None
                            if "abstract" in item:
                                abstract = item["abstract"]
                            publisher = None
                            if "publisher" in item:
                                publisher = item["publisher"]
                            if cit.doi is None:
                                cit.doi = doi
                            if cit.abstract is None:
                                cit.abstract = cit.abstract
                            if cit.publisher is None:
                                cit.publisher = cit.publisher
                        except BaseException as e:
                            print(e)
                            pass
                    logging.info("update cit from extsearch: " +
                                 str(cit.__dict__))
        with open("citations.json", "w+") as f:
            to_write = [cit.__dict__ for cit in cits.values()]
            json.dump(to_write, f)
