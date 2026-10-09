from __future__ import annotations

import logging
import re
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime
from difflib import SequenceMatcher
from functools import lru_cache
from urllib.parse import urljoin, urlparse

import requests
from bs4 import BeautifulSoup
from flask import Flask, jsonify, render_template, request

app = Flask(__name__)
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")

HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124 Safari/537.36",
    "Accept-Language": "me-ME,hr;q=0.9,en;q=0.8",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
}
TIMEOUT = 14
CACHE_TTL = 300

MONTENEGRO_CITIES = [
    "Andrijevica", "Bar", "Berane", "Bijelo Polje", "Budva", "Cetinje",
    "Danilovgrad", "Gusinje", "Herceg Novi", "Kolašin", "Kotor", "Mojkovac",
    "Nikšić", "Petnjica", "Plav", "Plužine", "Pljevlja", "Podgorica", "Rožaje",
    "Šavnik", "Tivat", "Tuzi", "Ulcinj", "Zeta", "Žabljak"
]

AGENCIES = [
    {
    "id": "sitngo",
    "name": "SitnGo",
    "home": "https://sitngo.me/",
    "pages": [
        "https://sitngo.me/en/cars/"
    ],
    "cities": [
        "Podgorica",
        "Tivat",
        "Budva"
    ],
},
    {
        "id": "meridian", "name": "Meridian Rent a Car", "home": "https://meridian-rentacar.com/",
        "pages": ["https://meridian-rentacar.com/cars/?lang=me"],
        "cities": ["Podgorica", "Tivat", "Budva", "Bar", "Kotor", "Herceg Novi", "Ulcinj"],
    },
    {
        "id": "rentacars", "name": "RentaCars.me", "home": "https://rentacars.me/",
        "pages": ["https://rentacars.me/"],
        "cities": ["Podgorica", "Budva", "Kotor", "Bar", "Tivat", "Herceg Novi", "Ulcinj"],
    },
    {
        "id": "driver", "name": "Driver Car Rent", "home": "https://www.drivercar.rent/en",
        "pages": ["https://www.drivercar.rent/en"],
        "cities": ["Budva", "Tivat", "Podgorica", "Bar", "Kotor", "Herceg Novi", "Petrovac", "Ulcinj"],
    },
    {
        "id": "getcar", "name": "GetCar.me / Adriatic", "home": "https://getcar.me/en",
        "pages": ["https://getcar.me/en/our-fleet"],
        "cities": ["Budva", "Tivat", "Podgorica", "Kotor", "Bar", "Herceg Novi"],
    },
    {
        "id": "terrae", "name": "Terrae Car", "home": "https://www.terraecar.com/me/",
        "pages": ["https://www.terraecar.com/me/fleet/"],
        "cities": ["Podgorica", "Tivat", "Budva", "Bar", "Kotor", "Herceg Novi", "Ulcinj"],
    },
    {
    "id": "planet",
    "name": "Planet Rent a Car",
    "home": "https://planetrentacar.me/",
    "pages": [
        "https://planetrentacar.me/cijene/"
    ],
    "cities": [
        "Podgorica",
        "Tivat",
        "Budva",
        "Kotor",
        "Bar",
        "Herceg Novi",
        "Ulcinj"
    ],
},
]

KNOWN_BRANDS = [
    "Alfa Romeo", "Audi", "BMW", "Chevrolet", "Citroen", "Cupra", "Dacia", "Fiat",
    "Ford", "Honda", "Hyundai", "Jeep", "Kia", "Mazda", "Mercedes", "Mini", "Nissan",
    "Opel", "Peugeot", "Renault", "Seat", "Skoda", "Suzuki", "Toyota", "Volkswagen", "Volvo"
]
CATEGORY_KEYWORDS = {
    "Mali auto": ["aygo", "yaris", "ignis", "panda", "up", "i10", "picanto", "polo", "clio", "corsa", "fabia"],
    "Kompakt": ["golf", "i30", "corolla", "auris", "focus", "astra", "megane", "ceed", "octavia"],
    "SUV": ["suv", "tiguan", "tucson", "vitara", "duster", "q3", "q5", "x3", "x5", "x7", "sportage", "kodiaq", "kamiq", "wrangler"],
    "Limuzina": ["318", "320", "520", "a4", "a6", "e200", "c200", "passat", "superb", "sedan", "limousine"],
    "Kombi / 7+ sjedišta": ["touran", "sharan", "trafic", "proace", "transporter", "van", "minivan", "7 seats", "8 seats", "9 seats"],
    "Kabriolet": ["cabrio", "convertible", "mustang", "beetle cabrio", "cooper cabrio"],
}

PRICE_RE = re.compile(r"(?:€|EUR\s*)\s*([0-9]{1,4}(?:[.,][0-9]{1,2})?)|([0-9]{1,4}(?:[.,][0-9]{1,2})?)\s*(?:€|EUR)", re.I)
YEAR_RE = re.compile(r"\b(20(?:0[5-9]|1\d|2\d))\b")
SEATS_RE = re.compile(r"\b([2-9])\s*(?:seats?|sjedista|sjedišta|mjesta|places?)\b", re.I)


def clean(value: str | None) -> str:
    return re.sub(r"\s+", " ", value or "").strip()


def norm(value: str | None) -> str:
    tr = str.maketrans("čćžšđČĆŽŠĐ", "cczsdCCZSD")
    return clean(value).translate(tr).lower()


def slug_tokens(value: str | None) -> list[str]:
    return re.findall(r"[a-z]+|\d+", norm(value))


def _canonical_token(token: str) -> str:
    aliases = {
        "vw": "volkswagen",
        "volkswagen": "volkswagen",
        "merc": "mercedes",
        "mercedesbenz": "mercedes",
    }
    return aliases.get(token, token)


def _close_token(a: str, b: str) -> bool:
    """
    Blaga tolerancija na tipografske greške samo za duže riječi.
    Npr. 'Hyndai' može pogoditi 'Hyundai', ali kratki modeli
    poput A3, A7, X5 ostaju strogo kontrolisani.
    """
    if a == b:
        return True

    if len(a) < 5 or len(b) < 5:
        return False

    return SequenceMatcher(None, a, b).ratio() >= 0.84


def matches_model(model: str, query: str) -> bool:
    query_tokens = [_canonical_token(t) for t in slug_tokens(query)]
    model_tokens = [_canonical_token(t) for t in slug_tokens(model)]

    if not query_tokens:
        return True

    if not model_tokens:
        return False

    for token in query_tokens:
        if token.isdigit():
            if token not in model_tokens:
                return False
            continue

        matched = any(
            model_token == token
            or (
                len(token) >= 3
                and model_token.startswith(token)
            )
            or _close_token(token, model_token)
            for model_token in model_tokens
            if not model_token.isdigit()
        )

        if not matched:
            return False

    return True

def guess_brand(model: str) -> str:
    nm = norm(model)
    for brand in sorted(KNOWN_BRANDS, key=len, reverse=True):
        if norm(brand) in nm:
            return brand
    return clean(model).split(" ")[0] if clean(model) else ""


def guess_category(model: str) -> str:
    nm = norm(model)
    for category, words in CATEGORY_KEYWORDS.items():
        if any(norm(w) in nm for w in words):
            return category
    return "Ostalo"


def guess_transmission(text: str) -> str:
    n = norm(text)
    if re.search(r"\b(automatic|automatik|automatski|auto)\b", n) or re.search(r"\bA\b", text):
        return "Automatski"
    if re.search(r"\b(manual|manuelni|manuel|rucni)\b", n) or re.search(r"\bM\b", text):
        return "Manuelni"
    return ""


def guess_fuel(text: str) -> str:
    n = norm(text)
    if "hybrid" in n or "hibrid" in n: return "Hibrid"
    if "electric" in n or "elektr" in n: return "Električni"
    if "diesel" in n or "dizel" in n: return "Dizel"
    if "petrol" in n or "gasoline" in n or "benzin" in n: return "Benzin"
    return ""


def extract_prices(text: str, max_price: float = 350.0) -> list[float]:
    prices = []

    for match in PRICE_RE.finditer(text):
        raw = match.group(1) or match.group(2)

        try:
            value = float(raw.replace(",", "."))

            if 8 <= value <= max_price:
                prices.append(value)
        except ValueError:
            continue

    return prices


def extract_price(text: str, days: int = 1) -> float | None:
    """
    Zajednički fallback za jednostavne kartice.
    Site-specific scraperi imaju svoja preciznija pravila.
    """
    daily_patterns = [
        r"(?:€|EUR)\s*([0-9]{1,3}(?:[.,][0-9]{1,2})?)\s*(?:/\s*(?:day|dan)|per\s+day|po\s+danu)",
        r"([0-9]{1,3}(?:[.,][0-9]{1,2})?)\s*(?:€|EUR)\s*(?:/\s*(?:day|dan)|per\s+day|po\s+danu)",
        r"(?:od|from)\s*(?:€|EUR)\s*([0-9]{1,3}(?:[.,][0-9]{1,2})?)",
        r"(?:od|from)\s*([0-9]{1,3}(?:[.,][0-9]{1,2})?)\s*(?:€|EUR)",
    ]

    for pattern in daily_patterns:
        match = re.search(pattern, text, re.I)

        if match:
            value = float(match.group(1).replace(",", "."))

            if 8 <= value <= 350:
                return value

    prices = list(dict.fromkeys(extract_prices(text)))

    if len(prices) == 1:
        return prices[0]

    return None


def best_model_text(card) -> str:
    candidates = []

    for sel in [
        "h1", "h2", "h3", "h4", "h5",
        ".title", ".name", ".car-name", ".vehicle-name",
        ".product-title", ".entry-title", "strong"
    ]:
        try:
            elements = card.select(sel)
        except Exception:
            elements = []

        for el in elements:
            txt = clean(el.get_text(" ", strip=True))

            if 3 <= len(txt) <= 90:
                candidates.append(txt)

    for img in card.find_all("img"):
        alt = clean(img.get("alt"))

        if 3 <= len(alt) <= 90:
            candidates.append(alt)

    bad_exact = {
        "reservation", "book now", "details", "view",
        "from", "per day", "rezervisi", "rezerviši",
        "opširnije", "opsirnije"
    }

    for txt in candidates:
        nt = norm(txt)

        if nt in bad_exact:
            continue

        if not re.search(r"[A-Za-zČĆŽŠĐčćžšđ]", txt):
            continue

        # Model mora ličiti na naziv vozila ili počinjati sa "Rent a".
        if any(norm(brand) in nt for brand in KNOWN_BRANDS) or nt.startswith("rent a ") or nt.startswith("vw "):
            return txt

    return ""


def direct_link(card, page_url: str) -> str:
    anchors = card.find_all("a", href=True)
    scored = []

    for a in anchors:
        href = clean(a.get("href"))

        if not href or href.startswith(("javascript:", "mailto:", "tel:")):
            continue

        url = urljoin(page_url, href)
        txt = norm(
            a.get_text(" ", strip=True)
            + " "
            + " ".join(a.get("class", []))
        )

        score = 0

        if any(k in txt for k in ["reserv", "book", "detail", "car", "vehicle", "rent", "opširnije", "opsirnije"]):
            score += 3

        if url != page_url and urlparse(url).path not in {"", "/", "/en", "/me"}:
            score += 2

        scored.append((score, url))

    return max(scored, default=(0, page_url), key=lambda x: x[0])[1]


@lru_cache(maxsize=128)
def fetch_html(url: str, bucket: int) -> tuple[str, str]:
    response = requests.get(
        url,
        headers=HEADERS,
        timeout=TIMEOUT,
        allow_redirects=True
    )
    response.raise_for_status()

    if not response.encoding or response.encoding.lower() in {
        "iso-8859-1",
        "windows-1252"
    }:
        response.encoding = response.apparent_encoding

    html = response.text

    # Popravka čestog UTF-8/latin1 mojibake problema.
    if "Å " in html or "Ä" in html or "Å¡" in html or "Å½" in html:
        try:
            repaired = html.encode("latin1").decode("utf-8")
            bad_before = html.count("Å") + html.count("Ä")
            bad_after = repaired.count("Å") + repaired.count("Ä")

            if bad_after < bad_before:
                html = repaired
        except (UnicodeEncodeError, UnicodeDecodeError):
            pass

    return html, response.url


def _brand_pattern() -> str:
    brands = sorted(
        set(KNOWN_BRANDS + ["VW", "ŠKODA", "SKODA"]),
        key=len,
        reverse=True
    )
    return "(?:" + "|".join(re.escape(x) for x in brands) + ")"


BRAND_PATTERN = _brand_pattern()


def _make_offer(
    agency: dict,
    model: str,
    price: float,
    source_url: str,
    source_page: str,
    text: str = "",
    year: int | None = None,
    transmission: str = "",
    fuel: str = "",
    seats: int | None = None,
    category: str | None = None,
) -> dict:
    model = clean(model)

    return {
        "agency": agency["name"],
        "agency_id": agency["id"],
        "model": model,
        "brand": guess_brand(model),
        "category": category or guess_category(model),
        "year": year,
        "transmission": transmission or guess_transmission(text),
        "fuel": fuel or guess_fuel(text),
        "seats": seats,
        "price_day": round(float(price), 2),
        "source_url": source_url,
        "source_page": source_page,
        "cities": agency["cities"],
    }


def _dedupe_offers(offers: list[dict]) -> list[dict]:
    unique = {}

    for item in offers:
        key = (
            norm(item.get("model", "")),
            item.get("price_day"),
            item.get("source_url", "")
        )
        unique[key] = item

    return list(unique.values())


def _result(
    agency: dict,
    offers: list[dict],
    message: str | None = None,
    errors: list[str] | None = None,
) -> dict:
    offers = _dedupe_offers(offers)
    errors = errors or []

    if message is None:
        if offers:
            message = f"Pronađeno {len(offers)} ponuda"
        elif errors:
            message = "Nije moguće pročitati ponude"
        else:
            message = "Sajt nije vratio odgovarajuće ponude"

    return {
        "agency": agency["name"],
        "agency_id": agency["id"],
        "ok": bool(offers),
        "count": len(offers),
        "offers": offers,
        "message": message,
    }


def _filter_query(offers: list[dict], query: str) -> list[dict]:
    if not query:
        return offers

    return [
        item for item in offers
        if matches_model(item.get("model", ""), query)
    ]


def _debug_result(
    agency: dict,
    url: str,
    before: list[dict],
    after: list[dict],
    query: str,
) -> None:
    print("\n==============================")
    print("AGENCIJA:", agency["name"])
    print("URL:", url)
    print("PRONADJENO PRIJE FILTERA:", len(before))

    for item in before[:10]:
        print(
            "-",
            item.get("model", "NEMA MODELA"),
            "| cijena:",
            item.get("price_day")
        )

    print("TRAZENI MODEL:", query if query else "NEMA FILTERA")
    print("PRONADJENO POSLIJE FILTERA:", len(after))

    for item in after[:10]:
        print(
            "  ->",
            item.get("model", "NEMA MODELA"),
            "| cijena:",
            item.get("price_day")
        )

    print("==============================\n")


def _select_price_from_tiers(
    days: int,
    tiers: list[tuple[int, int | None, float]]
) -> float | None:
    """
    tiers = [(1, 3, 70), (4, 7, 65), (8, 14, 60), (15, None, 55)]
    None kao gornja granica znači beskonačno.
    """
    for start, end, price in tiers:
        if days >= start and (end is None or days <= end):
            return price

    if tiers:
        # Ako sajt nema cijenu za duži period, uzmi posljednju javno
        # prikazanu dnevnu cijenu kao fallback.
        return tiers[-1][2]

    return None


# ============================================================
# SITNGO
# ============================================================

def scrape_sitngo(
    agency: dict,
    query: str = "",
    days: int = 1
) -> dict:

    url = agency["pages"][0]
    offers = []
    errors = []

    try:
        bucket = int(time.time() // CACHE_TTL)

        html, final_url = fetch_html(
            url,
            bucket
        )

        soup = BeautifulSoup(
            html,
            "html.parser"
        )

        # -------------------------------------------------
        # SITNGO
        #
        # Struktura na stranici je:
        #
        # Suzuki Ignis
        # 2020
        # M
        # 5
        # 5
        # €42 / day
        #
        # Toyota Yaris
        # 2020
        # A
        # 5
        # 5
        # €55 / day
        #
        # Zato tražimo LINK koji vodi na /cars/...
        # i predstavlja konkretno vozilo.
        # -------------------------------------------------

        vehicle_links = []

        for link in soup.find_all("a", href=True):

            href = clean(
                link.get("href", "")
            )

            model = clean(
                link.get_text(
                    " ",
                    strip=True
                )
            )

            if not href or not model:
                continue

            href_lower = href.lower()

            # Mora biti stranica konkretnog auta.
            # Primjer:
            # /en/cars/toyota-aygo/
            if "/cars/" not in href_lower:
                continue

            # Preskoči samu listu /cars/
            stripped_href = (
                href_lower
                .split("?")[0]
                .rstrip("/")
            )

            if stripped_href.endswith("/cars"):
                continue

            nmodel = norm(model)

            # Ne želimo Reservation, navigaciju itd.
            if nmodel in {
                "reservation",
                "cars",
                "all",
                "economy",
                "standard",
                "business",
                "premium",
                "suv",
                "cabriolets",
                "minivans",
            }:
                continue

            # Naziv mora ličiti na automobil.
            has_brand = any(
                norm(brand) in nmodel
                for brand in KNOWN_BRANDS
            )

            # Dodatni brandovi/varijante.
            if not has_brand:

                prefixes = (
                    "vw ",
                    "mini ",
                    "skoda ",
                    "škoda ",
                )

                if not nmodel.startswith(prefixes):
                    continue

            vehicle_links.append(link)

        # -------------------------------------------------
        # UKLANJANJE DUPLIKATA LINKOVA
        # -------------------------------------------------

        unique_links = []
        seen_links = set()

        for link in vehicle_links:

            model = clean(
                link.get_text(
                    " ",
                    strip=True
                )
            )

            href = urljoin(
                final_url,
                link.get("href")
            )

            key = (
                norm(model),
                href
            )

            if key in seen_links:
                continue

            seen_links.add(key)
            unique_links.append(link)

        # -------------------------------------------------
        # ČITANJE SVAKOG VOZILA
        # -------------------------------------------------

        for link in unique_links:

            model = clean(
                link.get_text(
                    " ",
                    strip=True
                )
            )

            source_url = urljoin(
                final_url,
                link.get("href")
            )

            # -------------------------------------------------
            # TRAŽIMO NAJMANJI RODITELJSKI BLOK
            # KOJI SADRŽI GODINU + M/A + €/DAY
            # -------------------------------------------------

            current = link
            car_block = None
            car_text = ""

            for _ in range(10):

                parent = current.parent

                if parent is None:
                    break

                text = clean(
                    parent.get_text(
                        " ",
                        strip=True
                    )
                )

                # mora sadržati godinu
                year_found = YEAR_RE.search(text)

                # mora sadržati EUR / day
                price_found = re.search(
                    r"€\s*\d+(?:[.,]\d+)?"
                    r"\s*/\s*day",
                    text,
                    re.I
                )

                # transmission M ili A
                transmission_found = re.search(
                    r"(?:^|\s)(M|A)(?:\s|$)",
                    text
                )

                if (
                    year_found
                    and price_found
                    and transmission_found
                ):
                    car_block = parent
                    car_text = text
                    break

                current = parent

            if car_block is None:
                continue

            # -------------------------------------------------
            # VAŽNO:
            #
            # Roditelj nekad može obuhvatiti i sljedeći auto.
            # Zato sve podatke uzimamo što bliže početku
            # trenutnog modela.
            # -------------------------------------------------

            start_position = (
                car_text
                .lower()
                .find(
                    model.lower()
                )
            )

            if start_position >= 0:
                car_text = car_text[
                    start_position:
                ]

            # -------------------------------------------------
            # GODINA
            # -------------------------------------------------

            year = None

            year_match = YEAR_RE.search(
                car_text
            )

            if year_match:
                try:
                    year = int(
                        year_match.group(1)
                    )
                except ValueError:
                    year = None

            # -------------------------------------------------
            # MJENJAČ
            # -------------------------------------------------

            transmission = ""

            # Tražimo M/A odmah poslije godine.
            if year:

                transmission_match = re.search(
                    rf"\b{year}\b"
                    r"\s+(M|A)\b",
                    car_text,
                    re.I
                )

            else:

                transmission_match = re.search(
                    r"(?:^|\s)(M|A)(?:\s|$)",
                    car_text,
                    re.I
                )

            if transmission_match:

                tr = (
                    transmission_match
                    .group(1)
                    .upper()
                )

                if tr == "A":
                    transmission = "Automatski"

                elif tr == "M":
                    transmission = "Manuelni"

            # -------------------------------------------------
            # CIJENA
            # -------------------------------------------------

            price_match = re.search(
                r"€\s*"
                r"([0-9]{1,3}(?:[.,][0-9]{1,2})?)"
                r"\s*/\s*day",
                car_text,
                re.I
            )

            if not price_match:
                continue

            try:
                price_day = float(
                    price_match
                    .group(1)
                    .replace(",", ".")
                )

            except ValueError:
                continue

            if not (
                5 <= price_day <= 500
            ):
                continue

            # -------------------------------------------------
            # SJEDIŠTA I VRATA
            #
            # Poslije:
            # YEAR M/A seats doors
            #
            # npr:
            # 2020 M 5 5
            # -------------------------------------------------

            seats = None

            if year:

                seats_match = re.search(
                    rf"\b{year}\b"
                    r"\s+[MA]"
                    r"\s+(\d{1,2})"
                    r"\s+\d{1,2}\b",
                    car_text,
                    re.I
                )

                if seats_match:
                    try:
                        seats = int(
                            seats_match.group(1)
                        )
                    except ValueError:
                        seats = None

            # -------------------------------------------------
            # CATEGORY / BODY TYPE
            #
            # Lista ne daje uvijek dovoljno pouzdano
            # kategoriju, pa je ne izmišljamo.
            # -------------------------------------------------

            offer = _make_offer(
                agency=agency,
                model=model,
                price=price_day,
                source_url=source_url,
                source_page=final_url,
                text=car_text,
                year=year,
                transmission=transmission,
            )

            if seats:
                offer["seats"] = seats

            offers.append(
                offer
            )

        # -------------------------------------------------
        # FALLBACK
        #
        # Ako SitnGo promijeni HTML kartice,
        # koristimo tekst cijele stranice.
        # -------------------------------------------------

        if not offers:

            full_text = clean(
                soup.get_text(
                    " ",
                    strip=True
                )
            )

            # Primjer:
            # Toyota Yaris 2020 A 5 5 €55 / day
            #
            # Ovdje eksplicitno navodimo marke da regex
            # ne proguta tekst iz navigacije.
            sitngo_brands = (
                r"Toyota|Hyundai|Suzuki|Skoda|Škoda|"
                r"Volkswagen|VW|MINI|Mini|Peugeot|"
                r"Renault|Kia|Ford|Opel|Audi|BMW|"
                r"Mercedes(?:-Benz)?|Fiat|Nissan|"
                r"Citroen|Citroën|Dacia|Seat"
            )

            pattern = re.compile(
                rf"\b"
                rf"(?P<model>"
                rf"(?:{sitngo_brands})"
                rf"\s+"
                rf"[A-Za-z0-9ČĆŽŠĐčćžšđ"
                rf"\-+ .]{{1,40}}?"
                rf")"
                rf"\s+"
                rf"(?P<year>20\d{{2}}|19\d{{2}})"
                rf"\s+"
                rf"(?P<tr>M|A)"
                rf"\s+"
                rf"(?P<seats>\d{{1,2}})"
                rf"\s+"
                rf"(?P<doors>\d{{1,2}})"
                rf".{{0,60}}?"
                rf"€\s*"
                rf"(?P<price>"
                rf"\d{{1,3}}"
                rf"(?:[.,]\d{{1,2}})?"
                rf")"
                rf"\s*/\s*day",
                re.I
            )

            for match in pattern.finditer(
                full_text
            ):

                model = clean(
                    match.group("model")
                )

                # -------------------------------------------------
                # Čišćenje eventualnog "Reservation"
                # -------------------------------------------------

                model = re.sub(
                    r"\bReservation\b.*$",
                    "",
                    model,
                    flags=re.I
                ).strip()

                try:
                    year = int(
                        match.group("year")
                    )

                    seats = int(
                        match.group("seats")
                    )

                    price_day = float(
                        match.group("price")
                        .replace(",", ".")
                    )

                except ValueError:
                    continue

                transmission = (
                    "Automatski"
                    if match.group("tr").upper() == "A"
                    else "Manuelni"
                )

                # Pokušaj da pronađemo pravi link.
                source_url = final_url

                model_link = soup.find(
                    "a",
                    string=lambda value: (
                        value
                        and norm(value) == norm(model)
                    )
                )

                if (
                    model_link
                    and model_link.get("href")
                ):
                    source_url = urljoin(
                        final_url,
                        model_link.get("href")
                    )

                offer = _make_offer(
                    agency=agency,
                    model=model,
                    price=price_day,
                    source_url=source_url,
                    source_page=final_url,
                    text=match.group(0),
                    year=year,
                    transmission=transmission,
                )

                offer["seats"] = seats

                offers.append(
                    offer
                )

        # -------------------------------------------------
        # DEDUPLIKATI
        # -------------------------------------------------

        offers = _dedupe_offers(
            offers
        )

        # -------------------------------------------------
        # FILTER PREMA UPITU
        # -------------------------------------------------

        filtered = _filter_query(
            offers,
            query
        )

        # -------------------------------------------------
        # DEBUG
        # -------------------------------------------------

        _debug_result(
            agency,
            final_url,
            offers,
            filtered,
            query
        )

        return _result(
            agency,
            filtered
        )

    except Exception as exc:

        error_message = (
            f"{type(exc).__name__}: {exc}"
        )

        errors.append(
            error_message
        )

        print(
            "\n!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"
        )
        print(
            "GRESKA SITNGO"
        )
        print(
            "URL:",
            url
        )
        print(
            "GRESKA:",
            error_message
        )
        print(
            "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n"
        )

        return _result(
            agency,
            [],
            errors=errors
        )

def scrape_planet(
    agency: dict,
    query: str = "",
    days: int = 1
) -> dict:

    url = agency["pages"][0]
    offers = []
    errors = []

    try:
        bucket = int(time.time() // CACHE_TTL)

        html, final_url = fetch_html(
            url,
            bucket
        )

        soup = BeautifulSoup(
            html,
            "html.parser"
        )

        # -------------------------------------------------
        # PLANET RENT A CAR
        #
        # Na stranici struktura izgleda približno:
        #
        # Citroen C3
        # Menjac: Manual 5 gears
        # 61 EUR
        # 54 EUR
        # 53 EUR
        # 51 EUR
        # 50 EUR
        # 100 EUR  <- depozit
        #
        # Zato svako vozilo tražimo preko linka/naziva,
        # pa onda čitamo njegov roditeljski red/blok.
        # -------------------------------------------------

        vehicle_links = []

        for link in soup.find_all("a", href=True):

            name = clean(
                link.get_text(
                    " ",
                    strip=True
                )
            )

            if not name:
                continue

            n = norm(name)

            # Mora izgledati kao naziv vozila.
            has_brand = any(
                norm(brand) in n
                for brand in KNOWN_BRANDS
            )

            # Planet ima typo "Hyndai".
            if (
                has_brand
                or n.startswith("vw ")
                or n.startswith("hyndai ")
            ):
                vehicle_links.append(link)

        # -------------------------------------------------
        # PROLAZ KROZ VOZILA
        # -------------------------------------------------

        for link in vehicle_links:

            model = clean(
                link.get_text(
                    " ",
                    strip=True
                )
            )

            if not model:
                continue

            # Ne uzimaj meni / navigaciju.
            if len(model) > 80:
                continue

            # -------------------------------------------------
            # NAĐI BLOK U KOJEM SU CIJENE
            # -------------------------------------------------

            block = link

            found_block = None

            # Penjemo se kroz roditelje dok ne nađemo
            # blok koji sadrži "Menjac" i dovoljno EUR cijena.
            for _ in range(8):

                parent = block.parent

                if parent is None:
                    break

                text = clean(
                    parent.get_text(
                        " ",
                        strip=True
                    )
                )

                eur_values = re.findall(
                    r"(\d+(?:[.,]\d+)?)\s*EUR",
                    text,
                    re.I
                )

                if (
                    ("menjac" in norm(text) or "mjenja" in norm(text))
                    and len(eur_values) >= 5
                ):
                    found_block = parent
                    break

                block = parent

            if found_block is None:
                continue

            block_text = clean(
                found_block.get_text(
                    " ",
                    strip=True
                )
            )

            # -------------------------------------------------
            # PROBLEM:
            # roditelj ponekad može sadržati više vozila.
            #
            # Zato izdvajamo dio od trenutnog modela
            # do sljedećeg modela / dovoljno podataka.
            # -------------------------------------------------

            start = block_text.lower().find(
                model.lower()
            )

            if start >= 0:
                block_text = block_text[start:]

            # -------------------------------------------------
            # MJENJAČ
            # -------------------------------------------------

            transmission = ""

            lowered = norm(block_text)

            if (
                "menjac automatic" in lowered
                or "menjac: automatic" in lowered
                or "automatic" in lowered
            ):
                transmission = "Automatski"

            elif (
                "menjac manual" in lowered
                or "menjac: manual" in lowered
                or "manual" in lowered
            ):
                transmission = "Manuelni"

            # -------------------------------------------------
            # CIJENE
            # -------------------------------------------------

            raw_prices = re.findall(
                r"(\d+(?:[.,]\d+)?)\s*EUR",
                block_text,
                re.I
            )

            prices = []

            for raw in raw_prices:

                try:
                    value = float(
                        raw.replace(",", ".")
                    )

                    prices.append(value)

                except ValueError:
                    continue

            # Planet mora imati:
            # 5 dnevnih cijena + depozit
            if len(prices) < 6:
                continue

            # Uzimamo PRVIH 5.
            # Šesta vrijednost je depozit.
            tier_prices = prices[:5]

            p_1_2 = tier_prices[0]
            p_3_6 = tier_prices[1]
            p_7_10 = tier_prices[2]
            p_11_14 = tier_prices[3]
            p_15_29 = tier_prices[4]

            # -------------------------------------------------
            # IZBOR CIJENE PREMA BROJU DANA
            # -------------------------------------------------

            if days <= 2:
                price_day = p_1_2

            elif days <= 6:
                price_day = p_3_6

            elif days <= 10:
                price_day = p_7_10

            elif days <= 14:
                price_day = p_11_14

            else:
                price_day = p_15_29

            # Sigurnosna provjera.
            if not (5 <= price_day <= 500):
                continue

            # -------------------------------------------------
            # GODINA
            # -------------------------------------------------

            year = None

            year_match = YEAR_RE.search(model)

            if year_match:
                try:
                    year = int(
                        year_match.group(1)
                    )
                except Exception:
                    year = None

            # -------------------------------------------------
            # CATEGORY
            # -------------------------------------------------

            category = ""

            # pokušaj pronaći kategoriju iz prethodnih headinga
            previous = link.find_previous(
                ["h2", "h3", "h4", "strong"]
            )

            if previous:

                previous_text = clean(
                    previous.get_text(
                        " ",
                        strip=True
                    )
                )

                possible_categories = {
                    "hatchback",
                    "sedan",
                    "station wagon",
                    "suv",
                    "convertible",
                    "luxury",
                    "compact mpv",
                    "minivan",
                }

                if norm(previous_text) in possible_categories:
                    category = previous_text

            # -------------------------------------------------
            # LINK
            # -------------------------------------------------

            source_url = urljoin(
                final_url,
                link.get("href")
            )

            # -------------------------------------------------
            # OFFER
            # -------------------------------------------------

            offer = _make_offer(
                agency=agency,
                model=model,
                price=price_day,
                source_url=source_url,
                source_page=final_url,
                text=block_text,
                year=year,
                transmission=transmission,
            )

            # Ako _make_offer dozvoljava naknadnu kategoriju:
            if category:
                offer["category"] = category

            offers.append(offer)

        # -------------------------------------------------
        # DEDUPLIKATI
        # -------------------------------------------------

        offers = _dedupe_offers(
            offers
        )

        # -------------------------------------------------
        # FILTER MODELA
        # -------------------------------------------------

        filtered = _filter_query(
            offers,
            query
        )

        # -------------------------------------------------
        # DEBUG
        # -------------------------------------------------

        _debug_result(
            agency,
            final_url,
            offers,
            filtered,
            query
        )

        return _result(
            agency,
            filtered
        )

    except Exception as exc:

        error_message = (
            f"{type(exc).__name__}: {exc}"
        )

        errors.append(
            error_message
        )

        print("\n!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
        print("GRESKA PLANET RENT A CAR")
        print("URL:", url)
        print("GRESKA:", error_message)
        print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n")

        return _result(
            agency,
            [],
            errors=errors
        )

# ============================================================
# MERIDIAN
# ============================================================

def scrape_meridian(agency: dict, query: str = "", days: int = 1) -> dict:
    url = agency["pages"][0]
    errors = []
    offers = []

    try:
        bucket = int(time.time() // CACHE_TTL)
        html, final_url = fetch_html(url, bucket)
        soup = BeautifulSoup(html, "html.parser")
        full = clean(soup.get_text(" ", strip=True))

        # Meridian blok:
        # MODEL ... CDW: 400€ 1-3 dana 50€ 4-6 dana 42.5€ 7+ dana 40€
        pattern = re.compile(
            rf"\b(?P<model>{BRAND_PATTERN}\s+[A-Za-z0-9ČĆŽŠĐčćžšđ .+\-/]{{1,55}}?)"
            rf"\s+(?P<spec>.*?)"
            rf"CDW:\s*[0-9]{{2,4}}\s*€"
            rf"\s*1\s*-\s*3\s*dana\s*(?P<p1>[0-9]{{1,3}}(?:[.,][0-9]{{1,2}})?)\s*€"
            rf"\s*4\s*-\s*6\s*dana\s*(?P<p2>[0-9]{{1,3}}(?:[.,][0-9]{{1,2}})?)\s*€"
            rf"\s*7\+\s*dana\s*(?P<p3>[0-9]{{1,3}}(?:[.,][0-9]{{1,2}})?)\s*€",
            re.I | re.S
        )

        for match in pattern.finditer(full):
            model = clean(match.group("model"))
            spec = clean(match.group("spec"))

            p1 = float(match.group("p1").replace(",", "."))
            p2 = float(match.group("p2").replace(",", "."))
            p3 = float(match.group("p3").replace(",", "."))

            price = _select_price_from_tiers(
                days,
                [
                    (1, 3, p1),
                    (4, 6, p2),
                    (7, None, p3),
                ]
            )

            offers.append(
                _make_offer(
                    agency=agency,
                    model=model,
                    price=price,
                    source_url=final_url,
                    source_page=final_url,
                    text=spec + " " + model,
                )
            )

        before = _dedupe_offers(offers)
        after = _filter_query(before, query)
        _debug_result(agency, final_url, before, after, query)

        return _result(agency, after)

    except Exception as exc:
        errors.append(f"{type(exc).__name__}: {exc}")
        print("GRESKA MERIDIAN:", errors[-1])
        return _result(agency, [], errors=errors)


# ============================================================
# GETCAR / ADRIATIC
# ============================================================

def scrape_getcar(agency: dict, query: str = "", days: int = 1) -> dict:
    url = agency["pages"][0]
    errors = []
    offers = []

    try:
        bucket = int(time.time() // CACHE_TTL)
        html, final_url = fetch_html(url, bucket)
        soup = BeautifulSoup(html, "html.parser")
        full = clean(soup.get_text(" ", strip=True))

        # GetCar:
        # MODEL YEAR - specs ... 1-3 days 70€ 4-7 days 65€ 8-14 days 60€
        pattern = re.compile(
            rf"\b(?P<model>{BRAND_PATTERN}\s+[A-Za-z0-9ČĆŽŠĐčćžšđ .+\-/]{{1,65}}?)"
            rf"\s+(?P<year>20\d{{2}})\s*-\s*"
            rf"(?P<spec>.*?)"
            rf"1\s*-\s*3\s*days\s*(?P<p1>[0-9]{{1,3}}(?:[.,][0-9]{{1,2}})?)\s*€"
            rf"\s*4\s*-\s*7\s*days\s*(?P<p2>[0-9]{{1,3}}(?:[.,][0-9]{{1,2}})?)\s*€"
            rf"\s*8\s*-\s*14\s*days\s*(?P<p3>[0-9]{{1,3}}(?:[.,][0-9]{{1,2}})?)\s*€",
            re.I | re.S
        )

        for match in pattern.finditer(full):
            model = clean(match.group("model"))
            spec = clean(match.group("spec"))

            p1 = float(match.group("p1").replace(",", "."))
            p2 = float(match.group("p2").replace(",", "."))
            p3 = float(match.group("p3").replace(",", "."))

            price = _select_price_from_tiers(
                days,
                [
                    (1, 3, p1),
                    (4, 7, p2),
                    (8, None, p3),
                ]
            )

            seats_match = re.search(
                r"\b([2-9])\s+passengers?\b",
                spec,
                re.I
            )

            seats = (
                int(seats_match.group(1))
                if seats_match
                else None
            )

            offers.append(
                _make_offer(
                    agency=agency,
                    model=model,
                    price=price,
                    source_url=final_url,
                    source_page=final_url,
                    text=spec + " " + model,
                    year=int(match.group("year")),
                    seats=seats,
                )
            )

        before = _dedupe_offers(offers)
        after = _filter_query(before, query)
        _debug_result(agency, final_url, before, after, query)

        return _result(agency, after)

    except Exception as exc:
        errors.append(f"{type(exc).__name__}: {exc}")
        print("GRESKA GETCAR:", errors[-1])
        return _result(agency, [], errors=errors)


# ============================================================
# TERRAE
# ============================================================

def scrape_terrae(agency: dict, query: str = "", days: int = 1) -> dict:
    url = agency["pages"][0]
    errors = []
    offers = []

    try:
        bucket = int(time.time() // CACHE_TTL)
        html, final_url = fetch_html(url, bucket)
        soup = BeautifulSoup(html, "html.parser")
        full = clean(soup.get_text(" ", strip=True))

        # Terrae:
        # Toyota Yaris AT Ekonomična klasa Automatik Image: ...
        # Od € 13.00 po danu ... Image5 Sedišta ... Opširnije
        class_pattern = (
            r"(?:Niža|Niza|Ekonomična|Ekonomicna|Kompakt|"
            r"Mini|Standard|Luxury|Full Size|Mini Van|Cabrio)"
            r"\s+klasa"
        )

        pattern = re.compile(
            rf"\b(?P<model>{BRAND_PATTERN}\s+[A-Za-z0-9ČĆŽŠĐčćžšđ .+\-/]{{1,45}}?)"
            rf"\s+(?P<class>{class_pattern})"
            rf"\s+(?P<tr>Manual|Automatik|Automatic)"
            rf"(?P<middle>.*?)"
            rf"Od\s*€\s*(?P<price>[0-9]{{1,3}}(?:[.,][0-9]{{1,2}})?)"
            rf"\s*po\s*danu"
            rf"(?P<tail>.*?)(?:Opširnije|Opsirnije)",
            re.I | re.S
        )

        for match in pattern.finditer(full):
            model = clean(match.group("model"))
            price = float(match.group("price").replace(",", "."))
            tr_raw = norm(match.group("tr"))

            transmission = (
                "Automatski"
                if tr_raw in {"automatik", "automatic"}
                else "Manuelni"
            )

            tail = clean(match.group("tail"))
            seats_match = re.search(
                r"Image\s*([2-9])\s*(?:Sedišta|Sjedista|Sjedišta)",
                tail,
                re.I
            )

            seats = (
                int(seats_match.group(1))
                if seats_match
                else None
            )

            cls = norm(match.group("class"))

            if "kompakt" in cls:
                category = "Kompakt"
            elif any(x in cls for x in ["niza", "niža", "ekonomic"]):
                category = "Mali auto"
            elif "mini van" in cls:
                category = "Kombi / 7+ sjedišta"
            elif "cabrio" in cls:
                category = "Kabriolet"
            else:
                category = guess_category(model)

            offers.append(
                _make_offer(
                    agency=agency,
                    model=model,
                    price=price,
                    source_url=final_url,
                    source_page=final_url,
                    text=match.group(0),
                    transmission=transmission,
                    seats=seats,
                    category=category,
                )
            )

        before = _dedupe_offers(offers)
        after = _filter_query(before, query)
        _debug_result(agency, final_url, before, after, query)

        return _result(agency, after)

    except Exception as exc:
        errors.append(f"{type(exc).__name__}: {exc}")
        print("GRESKA TERRAE:", errors[-1])
        return _result(agency, [], errors=errors)


# ============================================================
# RENTACARS.ME
# ============================================================

def _rentacars_card_candidates(soup: BeautifulSoup):
    """
    RentaCars je sajt na kojem su širi selektori ranije davali
    dobre rezultate. Zato su oni dozvoljeni SAMO u ovom scraperu.
    """
    selectors = [
        "article",
        ".car",
        ".cars-item",
        ".car-item",
        ".vehicle",
        ".vehicle-item",
        ".fleet-item",
        ".product",
        ".product-item",
        ".card",
        ".offer",
        ".offer-item",
        ".item",
        ".auto-item",
        "[class*='car-']",
        "[class*='vehicle']",
        "[class*='fleet']",
        "[class*='product']",
    ]

    seen = set()
    cards = []

    for selector in selectors:
        try:
            elements = soup.select(selector)
        except Exception:
            continue

        for card in elements:
            ident = id(card)

            if ident in seen:
                continue

            seen.add(ident)
            txt = clean(card.get_text(" ", strip=True))

            if not (15 <= len(txt) <= 1400):
                continue

            model = best_model_text(card)

            if not model:
                continue

            # RentaCars kartice mogu imati više brojeva.
            # Za otkrivanje kartice je dovoljno da postoji € vrijednost.
            if not PRICE_RE.search(txt):
                continue

            cards.append(card)

    return cards


def _rentacars_detail_link(card, page_url: str) -> str:
    for a in card.find_all("a", href=True):
        href = clean(a.get("href"))
        absolute = urljoin(page_url, href)

        if "/rent-a-car-" in absolute:
            return absolute

    return direct_link(card, page_url)


def _rentacars_price_for_days(text: str, days: int) -> float | None:
    tiers = []

    for match in re.finditer(
        r"(\d+)\s*-\s*(\d+)\s*(?:dana|days?)"
        r".{0,80}?"
        r"([0-9]{1,3}(?:[.,][0-9]{1,2})?)\s*€"
        r"\s*/\s*(?:dana|days?)",
        text,
        re.I | re.S
    ):
        start = int(match.group(1))
        end = int(match.group(2))
        price = float(match.group(3).replace(",", "."))
        tiers.append((start, end, price))

    plus_match = re.search(
        r"(\d+)\+\s*(?:dana|days?)"
        r".{0,80}?"
        r"([0-9]{1,3}(?:[.,][0-9]{1,2})?)\s*€",
        text,
        re.I | re.S
    )

    if plus_match:
        tiers.append(
            (
                int(plus_match.group(1)),
                None,
                float(plus_match.group(2).replace(",", "."))
            )
        )

    price = _select_price_from_tiers(days, tiers)

    if price is not None:
        return price

    # Fallback: cijena po danu sa kartice.
    daily = extract_price(text, days)

    if daily is not None:
        return daily

    # Posljednji fallback samo ZA RentaCars karticu.
    candidates = extract_prices(text)

    if candidates:
        return min(candidates)

    return None


def scrape_rentacars(agency: dict, query: str = "", days: int = 1) -> dict:
    url = agency["pages"][0]
    errors = []
    discovered = []

    try:
        bucket = int(time.time() // CACHE_TTL)
        html, final_url = fetch_html(url, bucket)
        soup = BeautifulSoup(html, "html.parser")

        # Prvo otkrij ponude na početnoj stranici.
        for card in _rentacars_card_candidates(soup):
            text = clean(card.get_text(" ", strip=True))
            model = best_model_text(card)

            if not model:
                continue

            # Filtriraj prije dodatnog detail requesta.
            if query and not matches_model(model, query):
                continue

            detail_url = _rentacars_detail_link(card, final_url)
            price = None
            detail_text = ""

            # Ako tražimo konkretan model, otvaramo detail stranicu
            # i uzimamo cijenu prema broju dana.
            if query and detail_url != final_url:
                try:
                    detail_html, detail_final_url = fetch_html(
                        detail_url,
                        bucket
                    )
                    detail_soup = BeautifulSoup(
                        detail_html,
                        "html.parser"
                    )
                    detail_text = clean(
                        detail_soup.get_text(" ", strip=True)
                    )
                    price = _rentacars_price_for_days(
                        detail_text,
                        days
                    )
                    detail_url = detail_final_url
                except Exception as detail_exc:
                    print(
                        "RentaCars detail fallback:",
                        type(detail_exc).__name__,
                        detail_exc
                    )

            if price is None:
                price = _rentacars_price_for_days(text, days)

            if price is None:
                continue

            source_text = detail_text or text

            year_match = YEAR_RE.search(source_text)
            seats_match = SEATS_RE.search(source_text)

            discovered.append(
                _make_offer(
                    agency=agency,
                    model=model,
                    price=price,
                    source_url=detail_url,
                    source_page=final_url,
                    text=source_text,
                    year=(
                        int(year_match.group(1))
                        if year_match
                        else None
                    ),
                    seats=(
                        int(seats_match.group(1))
                        if seats_match
                        else None
                    ),
                )
            )

        before = _dedupe_offers(discovered)
        after = _filter_query(before, query)
        _debug_result(agency, final_url, before, after, query)

        return _result(agency, after)

    except Exception as exc:
        errors.append(f"{type(exc).__name__}: {exc}")
        print("GRESKA RENTACARS:", errors[-1])
        return _result(agency, [], errors=errors)


# ============================================================
# DRIVER CAR RENT
# ============================================================

def scrape_driver(
    agency: dict,
    query: str = "",
    days: int = 5
) -> dict:
    """
    Driver Car Rent je dinamički rezervacioni sistem.
    Za njega koristimo pravi Chrome/Selenium, jer obični requests POST
    ne prolazi istu JS/autocomplete validaciju kao browser.
    """
    from datetime import datetime, timedelta

    errors = []
    offers = []
    browser = None

    try:
        # -------------------------------------------------
        # SELENIUM IMPORTI
        # -------------------------------------------------
        try:
            from selenium import webdriver
            from selenium.webdriver.common.by import By
            from selenium.webdriver.common.keys import Keys
            from selenium.webdriver.support.ui import WebDriverWait, Select
            from selenium.webdriver.support import expected_conditions as EC
            from selenium.common.exceptions import TimeoutException
        except ImportError as exc:
            raise RuntimeError(
                "Nedostaje Selenium. Instaliraj ga komandom: pip install selenium"
            ) from exc

        # -------------------------------------------------
        # DATUMI
        # -------------------------------------------------
        pickup_dt = datetime.now() + timedelta(days=1)
        return_dt = pickup_dt + timedelta(days=max(int(days), 1))

        pickup_date = pickup_dt.strftime("%d %b")
        return_date = return_dt.strftime("%d %b")

        home_url = "https://www.drivercar.rent/en"
        vehicles_url = "https://www.drivercar.rent/en/reservation/vehicles"

        # -------------------------------------------------
        # CHROME
        #
        # Selenium Manager u novijim Selenium verzijama sam pronalazi
        # odgovarajući ChromeDriver, pa nije potrebno ručno skidanje.
        # -------------------------------------------------
        options = webdriver.ChromeOptions()

        # Headless je brži i ne otvara novi prozor.
        # Ako Driver ikad blokira headless, samo zakomentariši ovu liniju.
        options.add_argument("--headless=new")
        options.add_argument("--window-size=1440,1200")
        options.add_argument("--disable-gpu")
        options.add_argument("--no-sandbox")
        options.add_argument("--disable-dev-shm-usage")
        options.add_argument("--disable-blink-features=AutomationControlled")
        options.add_argument(
            "--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/150.0.0.0 Safari/537.36"
        )

        browser = webdriver.Chrome(options=options)
        browser.set_page_load_timeout(40)

        wait = WebDriverWait(browser, 25)

        browser.get(home_url)

        # -------------------------------------------------
        # POMOĆNE FUNKCIJE
        # -------------------------------------------------
        def find_by_name(name: str):
            return wait.until(
                EC.presence_of_element_located(
                    (By.NAME, name)
                )
            )

        def js_set_value(element, value: str):
            browser.execute_script(
                """
                const el = arguments[0];
                const value = arguments[1];

                el.removeAttribute('readonly');
                el.removeAttribute('disabled');

                const proto = Object.getPrototypeOf(el);
                const descriptor = Object.getOwnPropertyDescriptor(
                    proto,
                    'value'
                );

                if (descriptor && descriptor.set) {
                    descriptor.set.call(el, value);
                } else {
                    el.value = value;
                }

                el.dispatchEvent(
                    new Event('input', {bubbles: true})
                );
                el.dispatchEvent(
                    new Event('change', {bubbles: true})
                );
                el.dispatchEvent(
                    new Event('blur', {bubbles: true})
                );
                """,
                element,
                value
            )

        def set_hidden(name: str, value: str):
            elements = browser.find_elements(
                By.NAME,
                name
            )

            for element in elements:
                browser.execute_script(
                    """
                    const el = arguments[0];
                    el.removeAttribute('disabled');
                    el.value = arguments[1];
                    el.setAttribute('value', arguments[1]);
                    el.dispatchEvent(
                        new Event('input', {bubbles: true})
                    );
                    el.dispatchEvent(
                        new Event('change', {bubbles: true})
                    );
                    """,
                    element,
                    value
                )

        def choose_location(
            field_name: str,
            location_text: str,
            location_id_name: str,
            office_id_name: str,
        ):
            """
            Prvo pokušava pravi autocomplete kao korisnik.
            Ako dropdown selector promijene, imamo JS fallback sa
            tačnim ID vrijednostima iz njihovog formulara.
            """
            field = find_by_name(field_name)

            browser.execute_script(
                "arguments[0].scrollIntoView({block: 'center'});",
                field
            )

            try:
                field.click()
                field.send_keys(
                    Keys.CONTROL,
                    "a"
                )
                field.send_keys(
                    Keys.BACKSPACE
                )
                field.send_keys("Podgorica")
            except Exception:
                js_set_value(
                    field,
                    "Podgorica"
                )

            # Sačekaj autocomplete.
            WebDriverWait(browser, 7).until(
                lambda d: (
                    len(
                        d.find_elements(
                            By.XPATH,
                            "//*[contains("
                            "translate(normalize-space(.), "
                            "'ABCDEFGHIJKLMNOPQRSTUVWXYZ', "
                            "'abcdefghijklmnopqrstuvwxyz'), "
                            "'podgorica airport')]"
                        )
                    ) > 0
                )
            )

            # Traži vidljivu opciju koja liči na autocomplete stavku.
            candidate_selectors = [
                ".ui-autocomplete li",
                ".autocomplete-suggestions *",
                ".autocomplete-items *",
                ".typeahead *",
                ".tt-menu *",
                "[role='listbox'] [role='option']",
                "[role='option']",
                ".dropdown-menu li",
                ".suggestions li",
            ]

            clicked = False

            for selector in candidate_selectors:
                try:
                    items = browser.find_elements(
                        By.CSS_SELECTOR,
                        selector
                    )
                except Exception:
                    items = []

                for item in items:
                    try:
                        txt = clean(item.text)

                        if (
                            item.is_displayed()
                            and "podgorica airport" in norm(txt)
                        ):
                            browser.execute_script(
                                "arguments[0].scrollIntoView({block: 'center'});",
                                item
                            )
                            browser.execute_script(
                                "arguments[0].click();",
                                item
                            )
                            clicked = True
                            break
                    except Exception:
                        continue

                if clicked:
                    break

            # Ako nijedan poznati selector nije pogodio, probaj generički
            # vidljivi element sa tačnim tekstom.
            if not clicked:
                generic = browser.find_elements(
                    By.XPATH,
                    "//*[contains("
                    "translate(normalize-space(.), "
                    "'ABCDEFGHIJKLMNOPQRSTUVWXYZ', "
                    "'abcdefghijklmnopqrstuvwxyz'), "
                    "'podgorica airport')]"
                )

                # Biramo najmanji vidljivi element, da ne kliknemo cijelu stranicu.
                visible = []

                for item in generic:
                    try:
                        if item.is_displayed():
                            size = item.size
                            area = (
                                max(size.get("width", 0), 1)
                                * max(size.get("height", 0), 1)
                            )
                            visible.append(
                                (area, item)
                            )
                    except Exception:
                        continue

                visible.sort(
                    key=lambda pair: pair[0]
                )

                for _, item in visible[:10]:
                    try:
                        txt = norm(item.text)

                        if "podgorica airport" in txt:
                            browser.execute_script(
                                "arguments[0].click();",
                                item
                            )
                            clicked = True
                            break
                    except Exception:
                        continue

            # Bez obzira na autocomplete, osiguraj tekst + hidden ID-jeve.
            field = find_by_name(field_name)

            js_set_value(
                field,
                location_text
            )

            set_hidden(
                location_id_name,
                "2135"
            )
            set_hidden(
                office_id_name,
                "110"
            )

            return clicked

        # -------------------------------------------------
        # PICK-UP LOKACIJA
        # -------------------------------------------------
        pickup_clicked = choose_location(
            "pickup_location",
            "Podgorica airport",
            "pickup_location_id",
            "pickup_office_id",
        )

        # -------------------------------------------------
        # RETURN LOKACIJA
        #
        # Ako postoji "Return at pick-up" checkbox i uključen je,
        # sajt može sam popuniti povratnu lokaciju. Ipak upisujemo
        # hidden vrijednosti da backend dobije kompletan formular.
        # -------------------------------------------------
        return_fields = browser.find_elements(
            By.NAME,
            "return_location"
        )

        if return_fields:
            try:
                return_clicked = choose_location(
                    "return_location",
                    "Podgorica airport",
                    "return_location_id",
                    "return_office_id",
                )
            except Exception:
                return_clicked = False

                js_set_value(
                    return_fields[0],
                    "Podgorica airport"
                )

                set_hidden(
                    "return_location_id",
                    "2135"
                )
                set_hidden(
                    "return_office_id",
                    "110"
                )
        else:
            return_clicked = False

            set_hidden(
                "return_location_id",
                "2135"
            )
            set_hidden(
                "return_office_id",
                "110"
            )

        # -------------------------------------------------
        # DATUMI I VRIJEME
        # -------------------------------------------------
        for field_name, value in [
            ("pickup_date", pickup_date),
            ("pickup_time", "12:00"),
            ("return_date", return_date),
            ("return_time", "12:00"),
        ]:
            elements = browser.find_elements(
                By.NAME,
                field_name
            )

            if elements:
                js_set_value(
                    elements[0],
                    value
                )

        # -------------------------------------------------
        # GODINE VOZAČA
        # -------------------------------------------------
        age_elements = browser.find_elements(
            By.NAME,
            "driver_age"
        )

        if age_elements:
            age = age_elements[0]

            try:
                if age.tag_name.lower() == "select":
                    select = Select(age)

                    try:
                        select.select_by_value("30")
                    except Exception:
                        select.select_by_visible_text("30")
                else:
                    js_set_value(
                        age,
                        "30"
                    )
            except Exception:
                js_set_value(
                    age,
                    "30"
                )

        # -------------------------------------------------
        # DEBUG PRIJE SUBMITA
        # -------------------------------------------------
        form_values = browser.execute_script(
            """
            const names = [
                'pickup_location',
                'pickup_location_id',
                'pickup_office_id',
                'return_location',
                'return_location_id',
                'return_office_id',
                'pickup_date',
                'pickup_time',
                'return_date',
                'return_time',
                'driver_age'
            ];

            const out = {};

            for (const name of names) {
                const el = document.querySelector(
                    `[name="${name}"]`
                );

                out[name] = el ? el.value : null;
            }

            return out;
            """
        )

        print(
            "\nDRIVER SELENIUM FORM:",
            form_values
        )
        print(
            "DRIVER AUTOCOMPLETE PICKUP:",
            pickup_clicked
        )
        print(
            "DRIVER AUTOCOMPLETE RETURN:",
            return_clicked
        )

        # -------------------------------------------------
        # SUBMIT
        # -------------------------------------------------
        submit_button = None

        button_candidates = browser.find_elements(
            By.XPATH,
            "//button[contains("
            "translate(normalize-space(.), "
            "'ABCDEFGHIJKLMNOPQRSTUVWXYZ', "
            "'abcdefghijklmnopqrstuvwxyz'), "
            "'show available cars')]"
            " | "
            "//input[@type='submit']"
        )

        for button in button_candidates:
            try:
                if button.is_displayed():
                    submit_button = button
                    break
            except Exception:
                continue

        if submit_button is None:
            raise RuntimeError(
                "Driver dugme 'Show available cars' nije pronađeno."
            )

        browser.execute_script(
            "arguments[0].scrollIntoView({block: 'center'});",
            submit_button
        )

        try:
            submit_button.click()
        except Exception:
            browser.execute_script(
                "arguments[0].click();",
                submit_button
            )

        # -------------------------------------------------
        # SAČEKAJ REZULTAT
        # -------------------------------------------------
        def result_ready(driver):
            url_ok = (
                "/reservation/vehicles"
                in driver.current_url
            )

            page = driver.page_source

            cars_ok = bool(
                re.search(
                    r"\bor\s+similar\b",
                    page,
                    re.I
                )
            )

            return (
                url_ok
                and cars_ok
            )

        try:
            WebDriverWait(
                browser,
                35
            ).until(
                result_ready
            )
        except TimeoutException:
            # Ako submit event nije odradio redirect, probaj submit samog
            # roditeljskog forma nakon što su vrijednosti već popunjene.
            try:
                browser.execute_script(
                    """
                    const btn = arguments[0];
                    const form = btn.closest('form');

                    if (form) {
                        if (form.requestSubmit) {
                            form.requestSubmit(btn);
                        } else {
                            form.submit();
                        }
                    }
                    """,
                    submit_button
                )

                WebDriverWait(
                    browser,
                    25
                ).until(
                    result_ready
                )

            except Exception as second_exc:
                raise RuntimeError(
                    "Driver nije otvorio stranicu sa dostupnim vozilima. "
                    f"Trenutni URL: {browser.current_url}"
                ) from second_exc

        # Daj JS-u još trenutak da ubaci cijene u kartice.
        try:
            WebDriverWait(
                browser,
                10
            ).until(
                lambda d: (
                    "book now"
                    in d.page_source.lower()
                    or "/day"
                    in d.page_source.lower()
                    or "not available"
                    in d.page_source.lower()
                )
            )
        except Exception:
            pass

        vehicles_html = browser.page_source
        final_url = browser.current_url

        print(
            "DRIVER SELENIUM URL:",
            final_url
        )

        # -------------------------------------------------
        # PARSIRANJE REZULTATA
        # -------------------------------------------------
        soup = BeautifulSoup(
            vehicles_html,
            "html.parser"
        )

        similar_nodes = soup.find_all(
            string=re.compile(
                r"or\s+similar",
                re.I
            )
        )

        print(
            "DRIVER 'OR SIMILAR' TEKSTOVA:",
            len(similar_nodes)
        )

        driver_brand_regex = re.compile(
            r"\b(?:"
            r"Hyundai|Peugeot|Citroën|Citroen|Toyota|"
            r"Volkswagen|VW|Skoda|Škoda|Renault|Ford|"
            r"Audi|BMW|Mercedes(?:-Benz)?|Kia|KIA|Opel|"
            r"Suzuki|Nissan|Fiat|Seat|Dacia|Mini"
            r")\b",
            re.I
        )

        seen_models = set()

        for node in similar_nodes:
            current = node.parent
            card = current

            # Penjemo se dok roditelj sadrži tačno jedno vozilo.
            for _ in range(20):
                if current is None:
                    break

                parent = current.parent

                if parent is None:
                    break

                parent_text = clean(
                    parent.get_text(
                        " ",
                        strip=True
                    )
                )

                similar_count = len(
                    re.findall(
                        r"\bor\s+similar\b",
                        parent_text,
                        re.I
                    )
                )

                if (
                    similar_count == 1
                    and len(parent_text) <= 12000
                ):
                    card = parent
                    current = parent
                    continue

                break

            card_text = clean(
                card.get_text(
                    " ",
                    strip=True
                )
            )

            # -------------------------------------------------
            # MODEL
            # -------------------------------------------------
            similar_match = re.search(
                r"^(.*?)\s+or\s+similar\b",
                card_text,
                re.I
            )

            if not similar_match:
                continue

            prefix = clean(
                similar_match.group(1)
            )

            brand_matches = list(
                driver_brand_regex.finditer(
                    prefix
                )
            )

            if not brand_matches:
                continue

            # npr. "suv CGAV Hyundai Bayon" -> "Hyundai Bayon"
            model = clean(
                prefix[
                    brand_matches[-1].start():
                ]
            )

            model_key = norm(model)

            if model_key in seen_models:
                continue

            seen_models.add(
                model_key
            )

            ntext = norm(
                card_text
            )

            # -------------------------------------------------
            # CIJENA / DAN
            # -------------------------------------------------
            price_day = None

            daily_patterns = [
                r"([0-9]+(?:[.,][0-9]{1,2})?)\s*€\s*/\s*day\b",
                r"€\s*([0-9]+(?:[.,][0-9]{1,2})?)\s*/\s*day\b",
                r"([0-9]+(?:[.,][0-9]{1,2})?)\s*EUR\s*/\s*day\b",
                r"([0-9]+(?:[.,][0-9]{1,2})?)\s*€\s*per\s+day\b",
            ]

            for pattern in daily_patterns:
                match = re.search(
                    pattern,
                    card_text,
                    re.I
                )

                if not match:
                    continue

                try:
                    value = float(
                        match.group(1)
                        .replace(",", ".")
                    )
                except ValueError:
                    continue

                if 5 <= value <= 1000:
                    price_day = value
                    break

            has_book_now = bool(
                re.search(
                    r"\bbook\s+now\b",
                    ntext,
                    re.I
                )
            )

            # Ako je dostupno, ali daily tekst nije uhvaćen,
            # ukupna cijena / broj dana je fallback.
            if (
                price_day is None
                and has_book_now
            ):
                money_values = []

                for money_match in re.finditer(
                    r"([0-9]+(?:[.,][0-9]{1,2})?)\s*€",
                    card_text,
                    re.I
                ):
                    try:
                        value = float(
                            money_match.group(1)
                            .replace(",", ".")
                        )
                    except ValueError:
                        continue

                    if 10 <= value <= 10000:
                        money_values.append(
                            value
                        )

                # Na Driver kartici total je veći od dnevne cijene.
                if money_values:
                    total_candidate = max(
                        money_values
                    )

                    price_day = (
                        total_candidate
                        / max(int(days), 1)
                    )

            explicitly_unavailable = any(
                marker in ntext
                for marker in [
                    "not available",
                    "issued",
                    "unavailable",
                    "reserved",
                ]
            )

            available = (
                price_day is not None
                or has_book_now
            )

            print(
                "\n------------------------------"
            )
            print(
                "DRIVER MODEL:",
                model
            )
            print(
                "DRIVER FULL TEXT:",
                card_text[:1800]
            )

            if not available:
                if explicitly_unavailable:
                    print(
                        "DRIVER STATUS: NIJE DOSTUPNO"
                    )
                else:
                    print(
                        "DRIVER STATUS: NEPOZNAT / NEMA CIJENE"
                    )
                continue

            if price_day is None:
                print(
                    "DRIVER STATUS: DOSTUPNO, ALI CIJENA NIJE PRONAĐENA"
                )
                continue

            price_day = round(
                float(price_day),
                2
            )

            print(
                "DRIVER STATUS: DOSTUPNO"
            )
            print(
                "DRIVER CIJENA/DAN:",
                price_day
            )

            # -------------------------------------------------
            # MJENJAČ / GORIVO
            # -------------------------------------------------
            transmission = ""

            if "automatic" in ntext:
                transmission = "Automatski"
            elif "manual" in ntext:
                transmission = "Manuelni"

            fuel = ""

            if "hybrid" in ntext:
                fuel = "Hibrid"
            elif "electric" in ntext:
                fuel = "Električni"
            elif "diesel" in ntext:
                fuel = "Dizel"
            elif "petrol" in ntext:
                fuel = "Benzin"

            source_url = final_url

            link = card.find(
                "a",
                href=True
            )

            if link:
                href = clean(
                    link.get(
                        "href",
                        ""
                    )
                )

                if href:
                    source_url = urljoin(
                        final_url,
                        href
                    )

            offer = _make_offer(
                agency=agency,
                model=model,
                price=price_day,
                source_url=source_url,
                source_page=final_url,
                text=card_text,
                transmission=transmission,
            )

            if fuel:
                offer["fuel"] = fuel

            offers.append(
                offer
            )

        # -------------------------------------------------
        # DEDUPE + FILTER
        # -------------------------------------------------
        offers = _dedupe_offers(
            offers
        )

        filtered = _filter_query(
            offers,
            query
        )

        print(
            "\n=============================="
        )
        print(
            "AGENCIJA: Driver Car Rent"
        )
        print(
            "URL:",
            final_url
        )
        print(
            "DATUM:",
            pickup_date,
            "->",
            return_date
        )
        print(
            "PRONADJENO PRIJE FILTERA:",
            len(offers)
        )

        for offer in offers[:15]:
            print(
                "-",
                offer.get("model"),
                "| cijena:",
                offer.get("price_day")
            )

        print(
            "TRAZENI MODEL:",
            query
        )
        print(
            "PRONADJENO POSLIJE FILTERA:",
            len(filtered)
        )

        for offer in filtered[:15]:
            print(
                "  ->",
                offer.get("model"),
                "| cijena:",
                offer.get("price_day")
            )

        print(
            "==============================\n"
        )

        return _result(
            agency,
            filtered
        )

    except Exception as exc:
        error_message = (
            f"{type(exc).__name__}: {exc}"
        )

        errors.append(
            error_message
        )

        print(
            "\n!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"
        )
        print(
            "GRESKA DRIVER CAR RENT"
        )
        print(
            "GRESKA:",
            error_message
        )
        print(
            "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n"
        )

        return _result(
            agency,
            [],
            errors=errors
        )

    finally:
        if browser is not None:
            try:
                browser.quit()
            except Exception:
                pass



# ============================================================
# MAPA SCRAPERA + GLAVNI ROUTER
# ============================================================

SCRAPERS = {
    "sitngo": scrape_sitngo,
    "meridian": scrape_meridian,
    "rentacars": scrape_rentacars,
    "getcar": scrape_getcar,
    "terrae": scrape_terrae,
    "driver": scrape_driver,
    "planet": scrape_planet,
}


def scrape_agency(
    agency: dict,
    query: str = "",
    days: int = 1
) -> dict:
    scraper = SCRAPERS.get(agency["id"])

    if scraper is None:
        return _result(
            agency,
            [],
            message="Scraper za ovaj izvor nije definisan"
        )

    return scraper(
        agency=agency,
        query=query,
        days=days
    )


def parse_days() -> int:
    raw = request.args.get("days") or request.args.get("dana") or "1"
    try:
        return max(1, min(60, int(raw)))
    except ValueError:
        return 1


def valid_float(name: str) -> float | None:
    raw = clean(request.args.get(name, ""))
    if not raw: return None
    try: return float(raw.replace(",", "."))
    except ValueError: return None


@app.route("/")
def index():
    return render_template(
        "index.html",
        cities=MONTENEGRO_CITIES,
        agencies=AGENCIES,
        brands=KNOWN_BRANDS,
        categories=list(CATEGORY_KEYWORDS.keys()) + ["Ostalo"],
    )


@app.route("/api/search")
@app.route("/api/pretrazi")
def search():
    started = time.perf_counter()

    # -------------------------------------------------
    # OSNOVNI FILTERI
    # -------------------------------------------------
    query = clean(
        request.args.get("model")
        or request.args.get("auto")
        or ""
    )[:80]

    brand = clean(
        request.args.get("brand")
        or request.args.get("marka")
        or ""
    )[:40]

    city = clean(
        request.args.get("city")
        or request.args.get("grad")
        or ""
    )[:40]

    category = clean(
        request.args.get("category")
        or request.args.get("kategorija")
        or ""
    )[:40]

    transmission = clean(
        request.args.get("transmission")
        or request.args.get("mjenjac")
        or ""
    )[:30]

    fuel = clean(
        request.args.get("fuel")
        or request.args.get("gorivo")
        or ""
    )[:30]

    agency_filter = clean(
        request.args.get("agency")
        or request.args.get("agencija")
        or ""
    )[:50]

    min_price = valid_float("min_price")
    if min_price is None:
        min_price = valid_float("min_cijena")

    max_price = valid_float("max_price")
    if max_price is None:
        max_price = valid_float("max_cijena")

    try:
        min_seats = int(
            request.args.get("seats")
            or request.args.get("sjedista")
            or 0
        )
    except (ValueError, TypeError):
        min_seats = 0

    min_seats = max(0, min_seats)

    sort_by = clean(
        request.args.get("sort")
        or "price_asc"
    )

    days = parse_days()

    # -------------------------------------------------
    # VAŽNO: MARKA + MODEL SE SPAJAJU ZA SCRAPERE
    #
    # Primjeri:
    # brand=Hyundai, model=i20        -> Hyundai i20
    # brand=Volkswagen, model=Golf 7 -> Volkswagen Golf 7
    # brand=Hyundai, model=Hyundai i20 -> Hyundai i20
    # samo brand=Hyundai             -> Hyundai
    # samo model=Golf 7              -> Golf 7
    # -------------------------------------------------
    if brand and query:
        brand_tokens = {
            _canonical_token(token)
            for token in slug_tokens(brand)
        }

        query_tokens = {
            _canonical_token(token)
            for token in slug_tokens(query)
        }

        # Ako je marka već upisana u model, ne dupliraj je.
        if brand_tokens and brand_tokens.issubset(query_tokens):
            scraper_query = query
        else:
            scraper_query = clean(
                f"{brand} {query}"
            )

    elif brand:
        scraper_query = brand

    else:
        scraper_query = query

    print("\n==============================")
    print("VOZICG PRETRAGA")
    print("MARKA:", brand or "NEMA")
    print("MODEL:", query or "NEMA")
    print(
        "UPIT KOJI IDE SCRAPERIMA:",
        scraper_query or "NEMA"
    )
    print("DANA:", days)
    print("==============================\n")

    # -------------------------------------------------
    # IZBOR AGENCIJA
    # -------------------------------------------------
    selected_agencies = []

    for ag in AGENCIES:
        if (
            agency_filter
            and norm(agency_filter) not in norm(
                ag["name"]
            )
        ):
            continue

        if city:
            agency_cities = {
                norm(c)
                for c in ag.get("cities", [])
            }

            if norm(city) not in agency_cities:
                continue

        selected_agencies.append(ag)

    statuses = []
    raw_offers = []

    # -------------------------------------------------
    # SCRAPING SVIH IZABRANIH AGENCIJA
    # -------------------------------------------------
    if selected_agencies:
        with ThreadPoolExecutor(
            max_workers=min(
                6,
                len(selected_agencies)
            )
        ) as pool:

            future_map = {
                pool.submit(
                    scrape_agency,
                    ag,
                    scraper_query,
                    days
                ): ag
                for ag in selected_agencies
            }

            for future in as_completed(
                future_map
            ):
                ag = future_map[future]

                try:
                    result = future.result()

                    if not isinstance(
                        result,
                        dict
                    ):
                        raise TypeError(
                            "Scraper nije vratio dict rezultat"
                        )

                except Exception as exc:
                    print(
                        f"GRESKA {ag['name']}: "
                        f"{type(exc).__name__}: {exc}"
                    )

                    result = {
                        "agency": ag["name"],
                        "agency_id": ag["id"],
                        "ok": False,
                        "count": 0,
                        "offers": [],
                        "message": (
                            "Greška pri čitanju sajta"
                        ),
                    }

                statuses.append({
                    "agency": result.get(
                        "agency",
                        ag["name"]
                    ),
                    "agency_id": result.get(
                        "agency_id",
                        ag["id"]
                    ),
                    "ok": bool(
                        result.get("ok")
                    ),
                    "count": int(
                        result.get("count", 0)
                        or 0
                    ),
                    "message": result.get(
                        "message",
                        ""
                    ),
                })

                result_offers = result.get(
                    "offers",
                    []
                )

                if isinstance(
                    result_offers,
                    list
                ):
                    raw_offers.extend(
                        result_offers
                    )

    # -------------------------------------------------
    # ZAVRŠNO FILTRIRANJE
    #
    # Scraperi već filtriraju pomoću scraper_query,
    # ali ovo ostaje kao zaštita da rezultat bude tačan.
    # -------------------------------------------------
    filtered = []

    for original_offer in raw_offers:
        if not isinstance(
            original_offer,
            dict
        ):
            continue

        offer_model = clean(
            original_offer.get(
                "model",
                ""
            )
        )

        if not offer_model:
            continue

        # MODEL
        # npr. "Golf 7" mora biti u "Volkswagen Golf 7"
        if (
            query
            and not matches_model(
                offer_model,
                query
            )
        ):
            continue

        # MARKA
        # Koristimo matches_model nad cijelim nazivom vozila,
        # a ne samo offer["brand"], zbog VW/Volkswagen i typo varijanti.
        if (
            brand
            and not matches_model(
                offer_model,
                brand
            )
        ):
            continue

        # KATEGORIJA
        if (
            category
            and norm(category) != norm(
                original_offer.get(
                    "category",
                    ""
                )
            )
        ):
            continue

        # MJENJAČ
        if (
            transmission
            and norm(transmission) != norm(
                original_offer.get(
                    "transmission",
                    ""
                )
            )
        ):
            continue

        # GORIVO
        if (
            fuel
            and norm(fuel) != norm(
                original_offer.get(
                    "fuel",
                    ""
                )
            )
        ):
            continue

        # SJEDIŠTA
        seats_value = original_offer.get(
            "seats"
        )

        if min_seats:
            if seats_value is None:
                continue

            try:
                if int(seats_value) < min_seats:
                    continue
            except (
                ValueError,
                TypeError
            ):
                continue

        # CIJENA
        try:
            price_day = float(
                original_offer.get(
                    "price_day"
                )
            )
        except (
            ValueError,
            TypeError
        ):
            continue

        if price_day <= 0:
            continue

        if (
            min_price is not None
            and price_day < min_price
        ):
            continue

        if (
            max_price is not None
            and price_day > max_price
        ):
            continue

        offer = dict(
            original_offer
        )

        offer["price_day"] = round(
            price_day,
            2
        )

        offer["days"] = days

        offer["total"] = round(
            price_day * days,
            2
        )

        # best se postavlja tek nakon sortiranja.
        offer.pop(
            "best",
            None
        )

        filtered.append(
            offer
        )

    # -------------------------------------------------
    # UKLONI DUPLIKATE IZMEĐU ISTIH PONUDA
    #
    # Ne spajamo različite agencije.
    # -------------------------------------------------
    unique = {}

    for offer in filtered:
        key = (
            offer.get(
                "agency_id",
                norm(
                    offer.get(
                        "agency",
                        ""
                    )
                )
            ),
            norm(
                offer.get(
                    "model",
                    ""
                )
            ),
            round(
                float(
                    offer.get(
                        "price_day",
                        0
                    )
                ),
                2
            ),
        )

        # Ako postoji duplikat, zadrži onaj sa konkretnijim linkom.
        existing = unique.get(key)

        if existing is None:
            unique[key] = offer
            continue

        old_url = clean(
            existing.get(
                "source_url",
                ""
            )
        )

        new_url = clean(
            offer.get(
                "source_url",
                ""
            )
        )

        if len(new_url) > len(old_url):
            unique[key] = offer

    filtered = list(
        unique.values()
    )

    # -------------------------------------------------
    # SORTIRANJE
    # -------------------------------------------------
    if sort_by == "price_desc":
        filtered.sort(
            key=lambda x: (
                -x["price_day"],
                norm(
                    x.get(
                        "model",
                        ""
                    )
                )
            )
        )

    elif sort_by == "model":
        filtered.sort(
            key=lambda x: (
                norm(
                    x.get(
                        "model",
                        ""
                    )
                ),
                x["price_day"]
            )
        )

    elif sort_by == "agency":
        filtered.sort(
            key=lambda x: (
                norm(
                    x.get(
                        "agency",
                        ""
                    )
                ),
                x["price_day"]
            )
        )

    else:
        # Default: najjeftinije prvo.
        sort_by = "price_asc"

        filtered.sort(
            key=lambda x: (
                x["price_day"],
                norm(
                    x.get(
                        "model",
                        ""
                    )
                ),
                norm(
                    x.get(
                        "agency",
                        ""
                    )
                )
            )
        )

    # -------------------------------------------------
    # NAJJEFTINIJA PONUDA
    # -------------------------------------------------
    if filtered:
        for offer in filtered:
            offer["best"] = False

        if sort_by == "price_asc":
            filtered[0]["best"] = True

    # -------------------------------------------------
    # STATUS AGENCIJA
    # -------------------------------------------------
    agency_order = {
        agency["id"]: index
        for index, agency in enumerate(
            AGENCIES
        )
    }

    statuses.sort(
        key=lambda x: agency_order.get(
            x.get(
                "agency_id"
            ),
            999
        )
    )

    elapsed = round(
        time.perf_counter() - started,
        2
    )

    print("\n==============================")
    print(
        "UKUPNO SIROVIH PONUDA:",
        len(raw_offers)
    )
    print(
        "UKUPNO POSLIJE FILTERA:",
        len(filtered)
    )

    for offer in filtered[:20]:
        print(
            "->",
            offer.get("agency"),
            "|",
            offer.get("model"),
            "|",
            offer.get("price_day"),
            "€/dan"
        )

    print(
        "VRIJEME:",
        elapsed,
        "s"
    )
    print("==============================\n")

    # -------------------------------------------------
    # JSON ODGOVOR
    # -------------------------------------------------
    return jsonify({
        "status": "ok",
        "offers": filtered,
        "ponude": filtered,
        "sources": statuses,
        "elapsed": elapsed,
        "filters": {
            "model": query,
            "brand": brand,
            "scraper_query": scraper_query,
            "city": city,
            "days": days,
            "category": category,
            "transmission": transmission,
            "fuel": fuel,
            "seats": min_seats,
            "min_price": min_price,
            "max_price": max_price,
            "sort": sort_by,
        },
    })

@app.route("/api/meta")
@app.route("/api/katalog")
def meta():
    return jsonify({
        "cities": MONTENEGRO_CITIES, "gradovi": MONTENEGRO_CITIES,
        "brands": KNOWN_BRANDS, "brendovi": KNOWN_BRANDS,
        "categories": list(CATEGORY_KEYWORDS.keys()) + ["Ostalo"],
        "agencies": [{"id": a["id"], "name": a["name"]} for a in AGENCIES],
    })


if __name__ == "__main__":
    print("\nVoziCG je pokrenut: http://127.0.0.1:5000\n")
    app.run(debug=True, port=5000)
