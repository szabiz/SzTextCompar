# Copyright 2026 szabiz
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SzTextCompar Application (TF-IDF & Winnowing algoritmusokkal bővítve)

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter import font as tkfont
import difflib
import re
import string
import os
import json
import hashlib
import webbrowser
import concurrent.futures
from pathlib import Path
from collections import Counter
import math
import threading
import html
import time
import io
import struct
import zlib
import zipfile
import posixpath
from urllib.parse import unquote
from html.parser import HTMLParser
from xml.etree import ElementTree as ET
from xml.sax.saxutils import escape as _xml_escape
from bisect import bisect_left, bisect_right

IRASJELEK = set(string.punctuation) | set("„”‘’—–…«»")

# Ennyi egymást követő szónak kell lennie egy Hagyományos Diff egyezési
# szakaszban ahhoz, hogy önálló, egyedi színnel jelölt és kattintható/ugorható
# blokk legyen. Rövidebb (pl. egyetlen gyakori szóból álló) egyezéseknél a
# teljes szövegen futó karakteres illesztés sok, egyformán "helyes" jelöltet
# találhat (pl. az "és" szó 80 helyen is előfordulhat) - ilyenkor a rákattintás
# szinte véletlenszerű, kontextusból kiragadott helyre ugorna a másik panelen,
# ami félrevezető. Az ilyen rövid egyezések ezért csak sima (nem kattintható)
# zöld kiemelést kapnak, a hosszabb, egyértelmű szakaszok viszont igen.
MIN_HDIFF_SZAVAK = 3

# ============================================================================
# MODUL SZINTŰ SEGÉDFÜGGVÉNYEK
# ----------------------------------------------------------------------------
# Ezek a függvények szándékosan a modul (fájl) legfelső szintjén vannak, nem
# az osztályon belül: (1) ez teszi lehetővé, hogy a ProcessPoolExecutor
# (multiprocessing) biztonságosan "pickle-özze" és átadja őket a háttérben
# futó Python-folyamatoknak - egy a Tkinter-ablakhoz kötött metódust nem
# lehetne átadni másik folyamatnak; (2) így egyszerűen újrafelhasználhatók a
# gyorsítótárazásnál és a kötegelt mappa-vizsgálatnál is.
#
# Minden itt szereplő algoritmus (Simhash, Winnowing, TF-IDF/koszinusz) egy
# nyilvánosan publikált, évtizedek óta szabadon alkalmazott matematikai
# módszer saját, önálló implementációja - nem tartalmaz külső, szerzői jogi
# védelem alatt álló kódot vagy szöveget.
# ============================================================================


# ============================================================================
# KÉTNYELVŰ FELÜLET – Magyar / English
# A nyelvváltás kizárólag a felület feliratait érinti; az elemzési algoritmusok
# és a belső számítások változatlanok maradnak.
# ============================================================================
APP_NAME = "SzTextCompar"
APP_VERSION = "1.0"

CURRENT_LANGUAGE = "en"

UI_TRANSLATIONS = {
    "hu": {},
    "en": {
        "SzTextCompar 1.0 - Szöveghasonlóság-elemző": "SzTextCompar 1.0 - Text Similarity Analyzer",
        "⬅ Vissza": "⬅ Back", "Nincs több visszavonható lépés.": "Nothing to undo.",
        "Sikeres visszalépés az előző állapotba.": "Successfully restored the previous state.",
        "Kétfájlos Összehasonlítás & Szöveghasonlóság": "Two-File Comparison & Text Similarity",
        "Mappa Mátrix – Szöveghasonlóság": "Folder Matrix – Text Similarity",
        "Számítás folyamatban…": "Calculation in progress…",
        "Nyiss meg két fájlt, vagy válassz ellenőrzési típust.": "Open two files or select an analysis type.",
        "Bal fájl megnyitása...": "Open Left File...", "Jobb fájl megnyitása...": "Open Right File...",
        "Bal mentése másként...": "Save Left As...", "Jobb mentése másként...": "Save Right As...",
        "Mentés másként": "Save As",
        "Támogatott szöveg- és dokumentumfájlok": "Supported text and document files",
        "Szövegfájlok (kiemelés nélkül)": "Text files (no highlights)",
        "Szövegfájl (kiemelés nélkül)": "Text file (no highlights)",
        "Milyen formátumban mentsem?": "Which format should I save it in?", "Tovább": "Next",
        "Mit mentsek?": "What should I save?",
        "A teljes szöveg, ahogy látom (kijelölésekkel, színekkel)": "The whole text, as I see it (with highlights and colors)",
        "Csak az egyezések": "Matches only", "Csak az eltérések": "Differences only",
        "Nincs menthető tartalom a választott szűrővel.": "There is nothing to save with the selected filter.",
        "Az egyezések és eltérések mentése a Visual Match View alapján történik: legalább {minimum} egymást követő azonos szó.": "Matches and differences are saved according to the Visual Match View: at least {minimum} consecutive identical words.",
        "Word dokumentum (kiemelésekkel)": "Word document (with highlights)",
        "OpenDocument szöveg (kiemelésekkel)": "OpenDocument text (with highlights)",
        "HTML oldal (kiemelésekkel)": "HTML page (with highlights)",
        "EPUB formátumba nem lehet menteni.": "Saving to EPUB is not supported.",
        "💾 Kép mentése": "💾 Save image", "Hullám mentése képként": "Save waveform as image",
        "SVG kép (vektoros)": "SVG image (vector)", "PNG kép": "PNG image",
        "Kivágás": "Cut", "Másolás": "Copy", "Beillesztés": "Paste", "Mindent kijelöl": "Select All",
        "Részletes vizualizáció": "Detailed Visualization",
        "Elemzés folyamatban…": "Analysis in progress…",
        "Nincs elég hosszú, egyértelmű egyezés.": "No sufficiently long, unambiguous match.",
        "Válassza ki a dokumentumok mappáját": "Select the folder containing the documents",
        "Szöveg és felirat fájlok": "Text and subtitle files", "Minden fájl": "All files",
        "Szövegfájlok": "Text files", "HTML fájlok": "HTML files",
        "Hierarchikus összehasonlítás (nem elérhető)": "Hierarchical comparison (not available)",
        "Szín": "Color", "Színek – találatok": "Colors – Matches", "Szín kiválasztása": "Choose color",
        "Kattints egy színre a módosításhoz.": "Click a color to change it.",
        "Egyezések vizuális nézete (8 szín, sorban ismétlődve)": "Visual Match View (8 colors, repeating)",
        "Hagyományos diff – jelentős egyező szakaszok (8 szín)": "Traditional Diff – significant matching sections (8 colors)",
        "Kijelölés és általános kiemelés": "Selection and general highlight",
        "Kijelölt egyezés háttere": "Selected match background", "Kijelölt egyezés szövege": "Selected match text",
        "Kijelölt diff blokk háttere": "Selected diff block background", "Rövid egyezés kiemelése": "Short match highlight",
        "EKG (hullámforma) ablak": "ECG (waveform) window", "Hullám vonala": "Waveform line",
        "Egyező szöveg kiemelése": "Matching text highlight", "Alapértelmezett": "Default",
        "Alkalmaz": "Apply", "Mégse": "Cancel",
        "Az eredeti fájl nem írható felül. Kérlek, adj meg másik fájlnevet!": "The original file cannot be overwritten. Please choose a different file name!",
        "Egyező szavak min.:": "Min. matching words:",
        "Mód:": "Mode:", "Indítás": "Start", "Elemzési mód": "Analysis mode",
        "📋 Összesítő Tábla & Hasonlósági Index": "📋 Summary Table & Similarity Index",
        "📊 Részletes vizualizáció": "📊 Detailed Visualization",
        "Diff beállítások": "Diff Options", "Szóközök mellőzése": "Ignore Spaces", "Írásjelek mellőzése": "Ignore Punctuation","Szinkron görgetés": "Synchronized Scrolling",
        "Bal: időbélyeg törlés": "Left: Remove Timestamps", "Jobb: időbélyeg törlés": "Right: Remove Timestamps",
        "Sorok szinkronizálása (Diff blokk)": "Synchronize Lines (Diff Block)",
        "🌐 HTML Riport": "🌐 HTML Report",
        "🔎 Egyezések vizuális nézete": "🔎 Visual Match View", "◀ Előző egyezés": "◀ Previous Match", "Következő egyezés ▶": "Next Match ▶",    
        "Bal fájl: (nincs betöltve)": "Left file: (not loaded)", "Jobb fájl: (nincs betöltve)": "Right file: (not loaded)",
        "Mappa kiválasztása és kötegelt vizsgálat...": "Select Folder and Run Batch Analysis...",
        "Gyorsítótár (cache) használata": "Use Cache", "Több CPU-mag (multiprocessing) használata": "Use Multiple CPU Cores (multiprocessing)",
        "Első Fájl ▲": "First File ▲", "Második Fájl": "Second File",
        "Winnowing Ujjlenyomat (%)": "Winnowing Fingerprint (%)", "TF-IDF Tartalmi Egyezés (%)": "TF-IDF Content Similarity (%)",
        "Simhash Egyezés (%)": "Simhash Similarity (%)",
        " 🔎 Egyezések ": " 🔎 Matches ", "Minimum pontos egyezés:": "Minimum exact match:", "szó (2–10)": "words (2–10)",
        "✕ Bezár": "✕ Close", "Egyezések": "Matches",
        "Szöveg / Felirat fájl megnyitása": "Open Text / Subtitle File", "Mentés": "Save", "Mentve": "Saved",
        "Siker": "Success", "Hiba": "Error", "Figyelem": "Warning", "Információ": "Information",
        "Részletes vizualizációk": "Detailed Visualizations",
        "A két dokumentum részletes, értelmezhető összehasonlítása": "Detailed, interpretable comparison of the two documents",
        "  Kulcsszavak  ": "  Keywords  ", "  Mondatritmus  ": "  Sentence Rhythm  ", "  Stilisztika  ": "  Style  ",
        "Egyedi szavak": "Unique Words", "TTR (%)": "TTR (%)", "Átl. szóhossz": "Avg. Word Length", "Átl. mondathossz": "Avg. Sentence Length",
        "  Közös N-gramok  ": "  Common N-grams  ", "  Szógyakoriság  ": "  Word Frequency  ",
        "Bal fájl – szó": "Left file – word", "Jobb fájl – szó": "Right file – word", "Db": "Count",
        "Nincs közös 4-szavas kifejezés.": "No common 4-word phrase.", "Mindkét fájl üres.": "Both files are empty.",
        "Mindkét szövegmezőnek tartalmaznia kell szöveget.": "Both text fields must contain text.",
        "Mindkét szövegmezőnek tartalmaznia kell szöveget az összesítő futtatásához!": "Both text fields must contain text to run the summary!",
        "Minden elemzési modul eredménye és az összesített hasonlósági index:": "Results of all analysis modules and the overall similarity index:",
        "  📋 Táblázat  ": "  📋 Table  ", "  📊 Grafikon  ": "  📊 Chart  ",
        "Vizsgálati Módszer / Metrika": "Analysis Method / Metric", "Mért Érték (%)": "Measured Value (%)",
        "Minősítés / Részletes Értékelés": "Classification / Detailed Evaluation",
        " 🎯 Súlyozott Összesített Szöveghasonlósági Index ": " 🎯 Weighted Overall Text Similarity Index ",
        "Alacsony / Csekély szöveghasonlóság": "Low / Little Text Similarity",
        "Alacsony / Önálló szövegek.": "Low / Distinct Texts.",
        "Mérsékelt / Hasonló téma vagy részbeni átfedés": "Moderate / Similar Topic or Partial Overlap",
        "Közepes egyezés vagy részleges átvétel.": "Moderate similarity or partial overlap.",
        "Közepes szerkezeti hasonlóság.": "Moderate structural similarity.", "Közepes szókészlet-átfedés.": "Moderate vocabulary overlap.",
        "Közepes halmaz-átfedés.": "Moderate set overlap.", "Alacsony / Eltérő mondatszerkezet.": "Low / Different sentence structure.",
        "Alacsony / Önálló szókészlet.": "Low / Distinct vocabulary.",
        "MAGAS / ERŐS SZÖVEGEGYEZÉS": "HIGH / STRONG TEXT MATCH",
        "MAGAS / ERŐS SZÖVEGEGYEZÉS (Winnowing ujjlenyomat)": "HIGH / STRONG TEXT MATCH (Winnowing fingerprint)",
        "MAGAS / ERŐS SZÖVEGEGYEZÉS (Mondatritmus egyezés)": "HIGH / STRONG TEXT MATCH (Sentence Rhythm)",
        "Átfogó Összehasonlító & Hasonlósági Index Jelentés": "Comprehensive Comparison & Similarity Index Report",
        "Átfogó Súlyozott Index: ": "Overall Weighted Index: ",
        "Winnowing Ujjlenyomat (szövegegyezés-vizsgálat)": "Winnowing Fingerprint (text match analysis)",
        "TF-IDF Súlyozott Tartalmi Elemzés (Precíz Cosine)": "TF-IDF Weighted Content Analysis (Precise Cosine)",
        "Mondatritmus & Struktúra (Parafrázis szűrő)": "Sentence Rhythm & Structure (Paraphrase Filter)",
        "Hagyományos Diff (Karakter/Sor)": "Traditional Diff (Character/Line)",
        "N-gram kifejezés-egyezés": "N-gram Phrase Matching",
        "Szókészlet (Cosine) hasonlóság": "Vocabulary (Cosine) Similarity",
        "Jaccard-hasonlóság (Halmaz alapú)": "Jaccard Similarity (Set-based)",
        "Stilisztikai elemzés (Szókincs gazdagság)": "Stylometric Analysis (Vocabulary Richness)",
        "Simhash Ujjlenyomat (Nyelvfüggetlen, gyors)": "Simhash Fingerprint (Language-independent, fast)",
        "N-gram Kifejezés Eredmény": "N-gram Phrase Result", "Hagyományos Diff Eredmény": "Traditional Diff Result",
        "Winnowing szövegegyezés-vizsgálat": "Winnowing text match analysis",
        "TF-IDF Tartalmi Elemzés": "TF-IDF Content Analysis", "Mondatritmus & Parafrázis Eredmény": "Sentence Rhythm & Paraphrase Result",
        "Szókészlet (Cosine) Hasonlóság Eredmény": "Vocabulary (Cosine) Similarity Result",
        "Jaccard Halmaz-hasonlóság Eredmény": "Jaccard Set Similarity Result", "Stilisztikai Elemzés Eredmény": "Stylometric Analysis Result",
        "Simhash Ujjlenyomat Eredmény": "Simhash Fingerprint Result",
        "HTML riport mentése": "Save HTML Report", "Átfogó jelentés mentése": "Save Comprehensive Report",
        "💾 Teljes Jelentés Mentése Fájlba...": "💾 Save Full Report to File...", "🌐 HTML Riport": "🌐 HTML Report", "Bezárás": "Close",
        "Mappában lévő fájlpárok elemzése…": "Analyzing file pairs in folder…",
        "Kötegelt mappa elemzés háttérben fut...": "Batch folder analysis running in background...",
        "Kötegelt vizsgálat kész. Összehasonlított fájlpárok: ": "Batch analysis complete. File pairs compared: ",
        "Nincs megjeleníthető adat.": "No displayable data.", "Mindkét szövegben szükség van legalább egy mondatra.": "Both texts must contain at least one sentence.",
        "Nyelv": "Language", "Névjegy": "About", "Magyar": "Hungarian", "English": "English", "Bal fájl": "Left file", "Jobb fájl": "Right file", "(nincs betöltve)": "(not loaded)",
        "szó": "word", "Szó": "Words", "Bal": "Left", "Jobb": "Right", "Nem találtam legalább 5 egymást követő azonos szót tartalmazó szakaszt.": "No section containing at least 5 consecutive identical words was found.",
        "SzTextCompar — vizuális egyezési riport": "SzTextCompar — visual match report",
        "🔎 SzTextCompar — vizuális egyezési riport": "🔎 SzTextCompar — visual match report",
        "A pontos egyezések azonos sorszámot (#) kapnak mindkét oldalon. Ez az egyezés helyét mutatja; önmagában nem bizonyít másolást vagy szerzői jogsértést.": "Exact matches receive the same number (#) on both sides. This shows the location of the match; by itself it does not prove copying or copyright infringement.",
        "📊 Metrikák": "📊 Metrics", "Vizsgálati módszer": "Analysis method", "Mért érték": "Measured value", "Leírás": "Description",
        "🎯 Súlyozott összesített szöveghasonlósági index:": "🎯 Weighted overall text similarity index:",
        "🟩 Pontos szövegegyezés": "🟩 Exact text match", "🔢 Azonos # = ugyanaz a szakasz": "🔢 Same # = same section",
        "📌 Egyezési szakaszok": "📌 Matching sections",
        # A HTML riport és az Összesítő Tábla metrika-neveihez és
        # leírásaihoz tartozó fordítások (lásd _szoveg_ertekeles és az
        # Összesítő Tábla ablak "adatok" listája).
        "Winnowing Ujjlenyomat": "Winnowing Fingerprint",
        "TF-IDF Súlyozott Tartalmi Elemzés": "TF-IDF Weighted Content Analysis",
        "N-gram (4-szavas) Kifejezés": "N-gram (4-word) Phrase",
        "Mondatritmus & Parafrázis": "Sentence Rhythm & Paraphrase",
        "Hagyományos Karakter Diff": "Traditional Character Diff",
        "Szókészlet (Cosine)": "Vocabulary (Cosine)",
        "Jaccard Halmaz-hasonlóság": "Jaccard Set Similarity",
        "Simhash Ujjlenyomat": "Simhash Fingerprint",
        "Stilisztika (Bal fájl TTR)": "Stylometry (Left File TTR)",
        "Stilisztika (Jobb fájl TTR)": "Stylometry (Right File TTR)",
        "Átrendezésbiztos ujjlenyomat-alapú szövegegyezés-vizsgálat": "Reordering-resistant fingerprint-based text match analysis",
        "Ritka szavak súlyozása alapú tematikus egyezés": "Topical similarity based on rare-word weighting",
        "Közös fix 4-szavas kifejezések aránya": "Proportion of common fixed 4-word phrases",
        "Mondathossz ritmusprofil-egyezés": "Sentence-length rhythm profile similarity",
        "Közvetlen karakteres egyezési arány": "Direct character-level match rate",
        "Stop-szűrt szókészlet egyezése": "Stop-word-filtered vocabulary similarity",
        "Egyedi szavak halmaz-átfedése": "Set overlap of unique words",
        "Nyelvfüggetlen Hamming-távolság alapú egyezés": "Language-independent match based on Hamming distance",
        "Szavak": "Words",
        "Mondat sorszáma": "Sentence number", "Szó": "Word",
        "📈 Teljes képernyő (EKG)": "📈 Full Screen (ECG)",
        "Egyezési hullám számítása…": "Calculating match waveform…",
        "Egyezési hullám – teljes képernyő": "Match Waveform – Full Screen",
        "Min. egyező szó:": "Min. matching words:",
        "✕ Kilépés (Esc)": "✕ Exit (Esc)", "F11 teljes/ablak": "F11 Full/Window", "⟲ Teljes": "⟲ Fit all",
        "Nincs egyezés itt": "No match here", "egyező szó": "matching word(s)",
        "Kattintás / húzás: ugrás mindkét szövegben  •  Görgő: nagyítás  •  Shift+görgő / jobb gomb húzása: eltolás":
            "Click / drag: jump in both texts  •  Wheel: zoom  •  Shift+wheel / right-drag: pan",
        "A stop-szavak nélküli, mindkét szövegben előforduló legerősebb kulcsszavak.": "The strongest keywords (excluding stop words) that appear in both texts.",
    }
}

def _nyelvi_fajl_betoltese():
    """Külső JSON nyelvi fájlok betöltése, biztonságos beépített tartalékokkal."""
    base = Path(__file__).resolve().parent / "languages"
    for lang in ("hu", "en"):
        fajl = base / f"{lang}.json"
        try:
            if fajl.exists():
                with open(fajl, "r", encoding="utf-8") as f:
                    adat = json.load(f)
                if isinstance(adat, dict):
                    UI_TRANSLATIONS.setdefault(lang, {}).update(adat)
        except Exception:
            pass

_nyelvi_fajl_betoltese()

# Dinamikus üzenetekhez használt részleges fordítások.
# Ezek lehetővé teszik, hogy az f-stringekben összeállított üzenetek is
# angolra váltsanak, ne csak az önálló widget-feliratok.
DYNAMIC_TRANSLATIONS = {
    "en": {
        "Nincs több visszavonható lépés.": "There are no more undo steps available.",
        "Sikeres visszalépés az előző állapotba.": "Successfully restored the previous state.",
        "Nyiss meg két fájlt, vagy válassz ellenőrzési típust.": "Open two files or select an analysis type.",
        "Számítás folyamatban…": "Calculation in progress…",
        "Vizuális egyezésvizsgálat:": "Visual match analysis:",
        "pontos szakasz kiemelve a két szövegben.": "exact sections highlighted in both texts.",
        "Pontos egyezés (": "Exact match (",
        " szó): ": " words): ",
        " szakasz a két szövegben.": " sections in the two texts.",
        "Nincs egyezés": "No matches",
        "Mindkét fájl üres.": "Both files are empty.",
        "Háttérszámolás folyamatban...": "Background calculation in progress...",
        "Részletes vizualizáció elkészült.": "Detailed visualization completed.",
        "💾 Mentés HTML fájlba...": "💾 Save as HTML...",
        "Részletes vizualizáció HTML mentése": "Save Detailed Visualization as HTML",
        "Részletes vizualizációs HTML riport elmentve:": "Detailed visualization HTML report saved to:",
        "Nem sikerült létrehozni a részletes vizualizációs HTML riportot:": "Could not create the detailed visualization HTML report:",
        "SzTextCompar — Részletes vizualizáció riport": "SzTextCompar — Detailed Visualization Report",
        "Nincs adat.": "No data.",
        "Nincs elég adat.": "Not enough data.",
        "Mutató": "Metric",
        "Mindkét szövegben szükség van legalább egy mondatra.": "Both texts must contain at least one sentence.",
        "Sorok szinkronizálva. Eltérő sorok száma:": "Lines synchronized. Number of differing lines:",
        "Nem sikerült megnyitni a fájlt:": "Could not open file:",
        "Sikeresen elmentve:": "Successfully saved to:",
        "Nem sikerült menteni:": "Could not save:",
        "Nem találtam időbélyeget ebben a szövegben.": "No timestamp was found in this text.",
        "Az időbélyegeket eltávolítottam.": "Timestamps have been removed.",
        "Nincs mit szinkronizálni - mindkét fájl üres.": "Nothing to synchronize — both files are empty.",
        "Nem sikerült menteni a jelentést:": "Could not save the report:",
        "A jelentést sikeresen elmentettük ide:": "The report was successfully saved to:",
        "HTML riport elmentve:": "HTML report saved to:",
        "Nem sikerült létrehozni a HTML riportot:": "Could not create the HTML report:",
        "Mindkét szövegmezőnek tartalmaznia kell szöveget az összesítő futtatásához!": "Both text fields must contain text to run the summary!",
        "Technikai részlet:": "Technical detail:",
        "Minden szó kisbetűsítve szerepel; mindkét lista külön a leggyakoribb szóval kezdődik.  ": "All words are shown in lowercase; each list starts with its most frequent word.  ",
        "Bal: ": "Left: ", "Jobb: ": "Right: ", "Szó: ": "Words: ", "Egyedi: ": "Unique: ",
        "Átl. mondat: ": "Avg. sentence: ", "db": "items", "karakter": "characters",
        "Közös, egymást követő 4-szavas kifejezések: ": "Common consecutive 4-word phrases: ",
        " db.": " items.", "Mondatritmus-egyezés: ": "Sentence-rhythm similarity: ",
        "%. A vonalak a mondatok szavainak számát mutatják.": "%. The lines show the number of words in each sentence.",
        "A nyers stilisztikai mutatók összehasonlítása (eltérő mértékegységek miatt elsősorban arányként értelmezendő). ": "Comparison of raw stylistic metrics (primarily interpreted as ratios because the units differ). ",
        "Pontos egyezés (": "Exact match (", " szó): ": " words): ",
        "Nincs megjeleníthető adat.": "No displayable data.",
        "Mindkét szövegmezőnek tartalmaznia kell szöveget a HTML riporthoz!": "Both text fields must contain text for the HTML report!",
        "A kiválasztott mappában legalább 2 db szöveg- vagy feliratfájl szükséges!": "The selected folder must contain at least 2 text or subtitle files!",
        "Számítás: ": "Calculation: ", " új fájlpár (": " new file pairs (", " találat a gyorsítótárban)...": " cache hits)...",
        "Fájlok betöltve: ": "Files loaded: ", ". Az elemzéshez kattints az 'Indítás' gombra!": ". Click 'Start' to begin the analysis!",
        "Nem sikerült megnyitni: ": "Could not open: ", "Nem sikerült menteni: ": "Could not save: ",
        "Sorok szinkronizálva. Eltérő sorok száma: ": "Lines synchronized. Number of differing lines: ",
        "A két dokumentum ujjlenyomatának egyezése:": "Fingerprint similarity between the documents:",
        "ÉRTÉKELÉS:": "EVALUATION:", "MIT MÉR?": "WHAT DOES IT MEASURE?", "MIÉRT HASZNOS?": "WHY IS IT USEFUL?",
        "FONTOS:": "IMPORTANT:", "HOGYAN ÉRTELMEZD?": "HOW SHOULD IT BE INTERPRETED?", "MIT NEM MÉR?": "WHAT DOES IT NOT MEASURE?",
        "PÉLDA:": "EXAMPLE:", "BAL FÁJL:": "LEFT FILE:", "JOBB FÁJL:": "RIGHT FILE:",
        "A szavakból képzett rövid, egymást követő szókapcsolatok (ujjlenyomatok) közös arányát.": "The proportion of shared short consecutive word sequences (fingerprints).",
        "Kisebb beszúrások vagy a bekezdések átrendezése kevésbé torzítja, ezért jó átvett szövegrészek előszűrésére.": "Small insertions or paragraph reordering affect it less, making it useful for pre-screening potentially shared passages.",
        "A százalék nem szó szerinti egyezési arány és önmagában nem bizonyít másolást vagy szerzői jogsértést; ": "The percentage is not a literal word-for-word match rate and does not by itself prove copying or copyright infringement; ",
        "a találatokat a vizuális egyezésnézetben érdemes ellenőrizni.": "matches should be verified in the visual match view.",
        "A ritka szavakkal súlyozott TF-IDF egyezés:": "TF-IDF similarity weighted by rare words:",
        "MIT MÉR? A ritkább, tartalmi szavak közös jelenlétét és gyakoriságát.": "WHAT DOES IT MEASURE? The shared presence and frequency of rarer content words.",
        "A nagyon általános stop-szavak (pl. „és”, „a”, „hogy”) nem kapnak súlyt.": "Very common stop words are not weighted.",
        "A szavak sorrendje és a mondatok jelentése nem része a mérésnek.": "Word order and sentence meaning are not part of this measurement.",
        "Azonos témájú, de önálló szövegek is kaphatnak magas értéket.": "Independent texts on the same topic may also receive a high value.",
        "A két szöveg mondathossz-ritmusának egyezése:": "Similarity of sentence-length rhythm between the two texts:",
        "Bal fájl mondatainak száma:": "Number of sentences in left file:", "Jobb fájl mondatainak száma:": "Number of sentences in right file:",
        "Ez a módszer a mondatok hosszát (szavak száma) hasonlítja össze": "This method compares sentence length (number of words)",
        "ha valaki parafrázissal másol, a szavak másak lehetnek, de a mondathossz ritmusa gyakran hasonló marad.": "when paraphrasing, the words may differ, but sentence-length rhythm often remains similar.",
        "Nem vizsgálja a közös szavakat vagy a mondatok jelentését, csak a szerkezetet.": "It does not examine shared words or sentence meaning, only structure.",
        "Az érték ezért jelzés, nem önálló bizonyíték.": "The value is therefore an indicator, not standalone evidence.",
        "A két szöveg karakteres egyezési aránya:": "Character-level similarity between the two texts:",
        "Bal fájl hossza:": "Left file length:", "Jobb fájl hossza:": "Right file length:",
        "Ez a módszer a legegyszerűbb, közvetlen karakter-egyezést vizsgál": "This method examines the simplest direct character-level match",
        "Betűket, szóközöket és írásjeleket hasonlít össze a szöveg eredeti sorrendjében.": "It compares letters, spaces and punctuation in their original order.",
        "Ezért szó szerinti vagy közel szó szerinti másolatoknál a leghasznosabb.": "It is therefore most useful for verbatim or near-verbatim copies.",
        "A két szöveg 4-szavas kifejezés-egyezése:": "4-word phrase similarity between the two texts:",
        "Közös 4-szavas kifejezések száma:": "Number of common 4-word phrases:",
        "Ez a módszer fix 4-szavas kifejezéseket keres": "This method searches for fixed 4-word phrases",
        "ha a szerző több egymást követő szót változatlanul átemelt, azt ez felismeri.": "if several consecutive words were carried over unchanged, this method detects them.",
        "Az egyedi, közös 4-szavas sorozatok arányát; a szógyakoriságot nem számolja külön.": "The proportion of unique shared 4-word sequences; it does not separately count word frequency.",
        "A „Egyezések vizuális nézete” ablakban a minimális pontos egyezés hossza 2–10 szó között állítható.": "In the “Visual Match View”, the minimum exact-match length can be set from 2–10 words.",
        "A két dokumentum szókészletének koszinusz hasonlósága:": "Cosine similarity of the two documents' vocabularies:",
        "Ez a mutató a stop-szavak kiszűrése után a megmaradó tartalmi szavak vektoriális egyezését méri": "After removing stop words, this metric measures the vector similarity of the remaining content words",
        "A szavak sorrendjét és a pontos idézeteket nem keresi.": "It does not search for word order or exact quotations.",
        "Akkor magas, ha hasonló tartalmi szavak hasonló arányban fordulnak elő.": "It is high when similar content words occur in similar proportions.",
        "A két szöveg egyedi szavainak halmaz-átfedése:": "Set overlap of the unique words in the two texts:",
        "Ez a módszer az egyedi szavak halmazát hasonlítja össze": "This method compares the sets of unique words",
        "a szavak gyakoriságát nem veszi figyelembe, csak azt, hogy mely szavak szerepelnek mindkét dokumentumban.": "it ignores word frequency and only considers which words occur in both documents.",
        "Egy százszor leírt szó ugyanannyit számít, mint egy egyszer szereplő szó.": "A word written one hundred times counts the same as a word appearing once.",
        "A sorrendet és a mondatok jelentését sem vizsgálja.": "It does not examine order or sentence meaning.",
        "A két szöveg stilisztikai profilja:": "Stylometric profile of the two texts:",
        "Összes szó:": "Total words:", "Egyedi szó:": "Unique words:", "TTR (szókincsgazdagság):": "TTR (vocabulary richness):",
        "Átlagos szóhossz:": "Average word length:", "Átlagos mondat hossz:": "Average sentence length:",
        "A TTR (Type-Token Ratio) azt mutatja, hogy a szöveg mennyire változatos szókincset használ": "TTR (Type-Token Ratio) indicates how varied the vocabulary is",
        "magasabb érték gazdagabb, alacsonyabb érték ismétlődőbb szókincset jelent.": "a higher value indicates richer vocabulary, while a lower value indicates more repetition.",
        "A különbségek a szerzői hangról, műfajról vagy szöveghosszról is adódhatnak.": "Differences may also result from authorial voice, genre, or text length.",
        "A dokumentumok Simhash-ujjlenyomatának egyezése:": "Similarity of the documents' Simhash fingerprints:",
        "egy 64 bites ujjlenyomatot készít, majd e két ujjlenyomat biteltérését méri": "creates a 64-bit fingerprint and then measures the bit difference between the two fingerprints",
        "Magas érték hasonló általános szóhasználatra utal, de NEM azt jelenti,": "A high value indicates similar general word usage, but it does NOT mean",
        "hogy a szövegek ennyi százalékban szó szerint azonosak. Gyors előszűrésre való,": "that the texts are literally identical by this percentage. It is intended for quick pre-screening,",
        "és nem mutatja meg az egyezések helyét.": "and does not show where matches occur.",
        "Stilisztikai elemzés elkészült.": "Stylometric analysis completed.",
        "Túl rövidek a szövegek az N-gram vizsgálathoz.": "The texts are too short for N-gram analysis.",
        # A párbeszédablakok üzenetei szegmensenként épülnek fel, ezért ezeket
        # a hiányzó mondat-/kifejezés-darabokat is fel kell venni, különben a
        # végeredmény vegyes nyelvű marad (részben magyar, részben angol).
        "A dokumentumok ujjlenyomatának egyezése:": "Similarity of the documents' fingerprints:",
        "Magas érték rendszerint közös témára vagy közös kulcsfogalmakra utal.": "A high value usually indicates a shared topic or shared key concepts.",
        "Eltérő karakterek száma:": "Number of differing characters:",
        "átrendezésre vagy parafrázisra nem érzékeny.": "it is not sensitive to reordering or paraphrasing.",
        "a szavak előfordulási gyakorisága alapján.": "based on how frequently the words occur.",
        "Nem tartalmi egyezést vagy másolást, hanem két külön szöveg stílusjegyeit.": "Not content similarity or copying, but the stylistic traits of two separate texts.",
        "A szavak és szógyakoriságok teljes szövegszintű mintázatából ": "From the overall pattern of words and word frequencies across the whole text, it ",
        "(Hamming-távolság).": "(Hamming distance).",
        "Ez a mutató parafrázisokat (átfogalmazott, de azonos jelentésű mondatokat) is felismer.": "This metric also recognizes paraphrases (sentences that are reworded but carry the same meaning).",
        # A "Kötegelt Mappa Mátrix" és "Összesítő Tábla" ablakok saját,
        # kissé eltérő szóhasználatú metrika-listával dolgoznak.
        "Ujjlenyomat-alapú szövegegyezés-vizsgálat (átrendezésbiztos)": "Fingerprint-based text match analysis (reordering-resistant)",
        "Ritka szavak súlyozása alapú precíz tematikus egyezés": "Precise topical similarity based on rare-word weighting",
        "Stop-szűrt alap szókészlet egyezése": "Basic stop-word-filtered vocabulary similarity",
        "Mondathossz ritmusprofil | Mondatok: ": "Sentence-length rhythm profile | Sentences: ",
        "Nyelvfüggetlen, Hamming-távolság alapú gyors ujjlenyomat-egyezés": "Language-independent quick fingerprint match based on Hamming distance",
        "Átfogó Súlyozott Index: ": "Overall Weighted Index: ",
        "=== SABTEXTCOMPAR - SZÖVEGHASONLÓSÁGI JELENTÉS ===": "=== SABTEXTCOMPAR - TEXT SIMILARITY REPORT ===",
        "ÖSSZESÍTETT SZÖVEGHASONLÓSÁGI / EGYEZÉSI INDEX: ": "OVERALL TEXT SIMILARITY / MATCH INDEX: ",
        "MINŐSÍTÉS: ": "CLASSIFICATION: ",
        "Módszer: ": "Method: ", "Érték:   ": "Value:   ", "Elemzés: ": "Analysis: ",
        "szó": "words",
        # Ebben a körben talált, korábban egyáltalán nem fordított
        # feliratok (Mappa Mátrix tipp, Egyezések panel, HTML mentés
        # visszaigazolás, állapotsor-üzenetek).
        "(Tipp: Kattints a fejlécbe a rendezéshez, vagy duplán a sorra a megnyitáshoz!)": "(Tip: Click a column header to sort, or double-click a row to open it!)",
        "pontos egyezési szakasz": "matching sections",
        "Legalább ": "At least ",
        " egymást követő azonos szó": " consecutive identical words",
        "Bal sor": "Left line", "Jobb sor": "Right line",
        "pontos szakasz kiemelve a két szövegben.": "matching sections highlighted in the two texts.",
        "A HTML riportot elmentettem ide:\n": "The HTML report has been saved to:\n",
        "\n\nMegnyitás böngészőben...": "\n\nOpening in browser...",
        "egyedi.": "unique.",
        "Bal fájl: ": "Left file: ", "Jobb fájl: ": "Right file: ",
        "Kötegelt vizsgálat kész. Összehasonlított fájlpárok: ": "Batch analysis complete. File pairs compared: ",
        " (Ebből gyorsítótárból: ": " (of which from cache: ", " db)": " items)",
        "[Winnowing] Ujjlenyomat egyezés:": "[Winnowing] Fingerprint match:",
        "[TF-IDF] Tartalmi egyezés:": "[TF-IDF] Content match:",
        "[Mondatritmus] Struktúra egyezés:": "[Sentence rhythm] Structure match:",
        "(Mondatok: ": "(Sentences: ",
        "[Diff] Eltérés:": "[Diff] Difference:", "Egyezés:": "Match:", "Egyezés ": "Match ",
        "[N-gram] Egyezés:": "[N-gram] Match:",
        "[Cosine] Hasonlóság:": "[Cosine] Similarity:", "[Jaccard] Hasonlóság:": "[Jaccard] Similarity:",
        "[Simhash] Ujjlenyomat egyezés:": "[Simhash] Fingerprint match:",
        " egyértelmű (≥": " unambiguous (≥",
        " szavas) egyezés (kattints egy kiemelt szakaszra az ugráshoz)": " words) matches (click a highlighted section to jump)",
        "Hierarchikus: ": "Hierarchical: ", " egyező mondat, ": " matching sentences, ",
        " karakteren Diff.": " characters compared with Diff.",
    }
}

def tr(text):
    # A widgetek felirataihoz gyakran teszünk kozmetikai célú szóköz-
    # kitöltést (pl. "  Kétfájlos Összehasonlítás & Szöveghasonlóság  "),
    # miközben a fordítási szótár kulcsai kitöltés nélküliek. Emiatt a
    # sima .get(text, text) hívás nem talált egyezést, és a felirat
    # némán megmaradt magyar nyelven. Megoldás: a kikeresés előtt
    # levágjuk a kitöltő szóközöket, majd a fordított szöveg köré
    # visszatesszük ugyanazt a kitöltést.
    # Két eltérő szótár-konvenció létezik a projektben: néhány kulcs
    # SZÁNDÉKOSAN tartalmazza a kozmetikai szóköz-kitöltést (pl.
    # "  Kulcsszavak  "), míg máshol (pl. Notebook fül-feliratok) a
    # widget kap kitöltést, de a szótárkulcs kitöltés nélküli. Ezért
    # előbb a pontos (eredeti) szöveggel próbálkozunk, és csak ha az
    # nem talál egyezést, esünk vissza a levágott változatra.
    ui_dict = UI_TRANSLATIONS.get(CURRENT_LANGUAGE, {})
    if text in ui_dict:
        return ui_dict[text]

    stripped = text.strip()
    leading = text[:len(text) - len(text.lstrip())]
    trailing = text[len(text.rstrip()):]

    stripped = text.strip()
    leading = text[:len(text) - len(text.lstrip())]
    trailing = text[len(text.rstrip()):]

    if stripped in ui_dict:
        return leading + ui_dict[stripped] + trailing

    if CURRENT_LANGUAGE == "en":
        # A visszaeső (dinamikus) fordítást a TELJES, eredeti (nem levágott)
        # szövegen futtatjuk. Ez azért fontos, mert néhány DYNAMIC_TRANSLATIONS
        # kulcs maga is tartalmaz szándékos szélső szóközt (pl. egy teljes
        # feliratként átadott mondat végén álló szóköz) - ha itt a már
        # levágott szöveget használnánk, az ilyen kulcsok sosem egyeznének.
        # A mondatba ágyazott (nem szélső) darabokat ez nem érinti.
        return _dinamikus_forditas(text)

    return text

_DINAMIKUS_MINTAK = None  # lazán, első híváskor épül fel (cache)

def _dinamikus_forditas(text):
    # A DYNAMIC_TRANSLATIONS bejegyzéseket NEM sima .replace()-szel cseréljük,
    # mert az szóhatár nélkül a hosszabb szavak belsejébe is belenyúlhat
    # (pl. "karakter" -> "characters" a "karakterek" szóban "charactersek"
    # torzult eredményt adna). Helyette Unicode-tudatos szóhatár-ellenőrzéssel
    # rendelkező reguláris kifejezéseket használunk: a csere csak akkor
    # történik meg, ha a kulcs eleje/vége ténylegesen szóhatáron van (vagy a
    # kulcs maga írásjellel/szóközzel kezdődik-végződik, ahol ez amúgy sem
    # kérdés). Hosszabb kifejezéseket előbb cserélünk, hogy egy hosszú
    # mondatrészlet ne törjön szét egy benne található rövidebb kulcs miatt.
    global _DINAMIKUS_MINTAK
    if _DINAMIKUS_MINTAK is None:
        elemek = []
        for hu, en in sorted(DYNAMIC_TRANSLATIONS["en"].items(), key=lambda x: len(x[0]), reverse=True):
            if not hu:
                continue
            minta = re.escape(hu)
            if re.match(r'\w', hu[0], re.UNICODE):
                minta = r'(?<!\w)' + minta
            if re.match(r'\w', hu[-1], re.UNICODE):
                minta = minta + r'(?!\w)'
            elemek.append((re.compile(minta, re.UNICODE), en))
        _DINAMIKUS_MINTAK = elemek
    for regex, en in _DINAMIKUS_MINTAK:
        text = regex.sub(lambda m, _en=en: _en, text)
    return text

def set_language(lang):
    global CURRENT_LANGUAGE
    CURRENT_LANGUAGE = lang if lang in ("hu", "en") else "hu"

def untr(text):
    if CURRENT_LANGUAGE == "hu":
        return text
    stripped = text.strip()
    leading = text[:len(text) - len(text.lstrip())]
    trailing = text[len(text.rstrip()):]
    for hu, en in UI_TRANSLATIONS["en"].items():
        if en == stripped:
            return leading + hu + trailing
    return text

# A widgetek létrehozásakor automatikusan fordítjuk a feliratokat.
_OriginalButton = ttk.Button
_OriginalLabel = ttk.Label
_OriginalCheckbutton = ttk.Checkbutton
_OriginalLabelFrame = ttk.LabelFrame
_OriginalCombobox = ttk.Combobox

def _localized_widget(cls):
    def factory(*args, **kwargs):
        if "text" in kwargs and isinstance(kwargs["text"], str):
            kwargs["text"] = tr(kwargs["text"])
        if cls is _OriginalCombobox and "values" in kwargs:
            kwargs["values"] = tuple(tr(v) if isinstance(v, str) else v for v in kwargs["values"])
        return cls(*args, **kwargs)
    return factory

ttk.Button = _localized_widget(_OriginalButton)
ttk.Label = _localized_widget(_OriginalLabel)
ttk.Checkbutton = _localized_widget(_OriginalCheckbutton)
ttk.LabelFrame = _localized_widget(_OriginalLabelFrame)
ttk.Combobox = _localized_widget(_OriginalCombobox)

_OriginalTkLabel = tk.Label
def _localized_tk_label(*args, **kwargs):
    if "text" in kwargs and isinstance(kwargs["text"], str):
        kwargs["text"] = tr(kwargs["text"])
    return _OriginalTkLabel(*args, **kwargs)
tk.Label = _localized_tk_label

_original_notebook_add = ttk.Notebook.add
def _localized_notebook_add(self, child, **kw):
    if isinstance(kw.get("text"), str):
        kw["text"] = tr(kw["text"])
    return _original_notebook_add(self, child, **kw)
ttk.Notebook.add = _localized_notebook_add

_original_tree_heading = ttk.Treeview.heading
def _localized_tree_heading(self, column, option=None, **kw):
    if isinstance(kw.get("text"), str):
        kw["text"] = tr(kw["text"])
    return _original_tree_heading(self, column, option, **kw)
ttk.Treeview.heading = _localized_tree_heading

# A rendszerüzenetek és fájlválasztók címei is a kiválasztott nyelvet használják.
_original_showinfo = messagebox.showinfo
_original_showwarning = messagebox.showwarning
_original_showerror = messagebox.showerror
def _msgwrap(fn):
    def wrapped(title, message, *args, **kwargs):
        return fn(tr(title), tr(message), *args, **kwargs)
    return wrapped
messagebox.showinfo = _msgwrap(_original_showinfo)
messagebox.showwarning = _msgwrap(_original_showwarning)
messagebox.showerror = _msgwrap(_original_showerror)

def _fajlvalaszto_burkolo(fn):
    """A fájlválasztók címe és fájltípus-felirata is a kiválasztott nyelven jelenik meg."""
    def wrapped(*args, **kwargs):
        if isinstance(kwargs.get("title"), str):
            kwargs["title"] = tr(kwargs["title"])
        if kwargs.get("filetypes"):
            kwargs["filetypes"] = [(tr(nev), minta) for nev, minta in kwargs["filetypes"]]
        return fn(*args, **kwargs)
    return wrapped
filedialog.askopenfilename = _fajlvalaszto_burkolo(filedialog.askopenfilename)
filedialog.asksaveasfilename = _fajlvalaszto_burkolo(filedialog.asksaveasfilename)
filedialog.askdirectory = _fajlvalaszto_burkolo(filedialog.askdirectory)

CACHE_VERZIO = "v3"  # v3: angol stopszavak + nyelvfelismerés - a régi cache-értékek érvénytelenek


def _stabil_hash64(token: str) -> int:
    """
    Determinisztikus, 64 bites, nyelvfüggetlen hash egy tokenre.
    (Az MD5 önmagában csak egy nyilvános, szabadon felhasználható
    kriptográfiai segédfüggvény a Python szabványkönyvtárból - nem
    számít önálló, szerzői jogvédett "műnek".)
    A beépített Python hash() függvénnyel ellentétben ez minden
    folyamatban/futtatásban ugyanazt az eredményt adja, ami elengedhetetlen
    a gyorsítótárazáshoz és a több-folyamatos (multiprocessing) számításhoz.
    """
    digest = hashlib.md5(token.encode("utf-8", errors="replace")).digest()
    return int.from_bytes(digest[:8], byteorder="big", signed=False)


def simhash_ertek(szoveg: str, hash_bitek: int = 64) -> int:
    """
    Simhash ujjlenyomat (Charikar, 2002 - "Similarity Estimation Techniques
    from Rounding Algorithms" - nyilvánosan publikált, szabadon
    implementálható algoritmus, akárcsak a Winnowing).

    Teljesen NYELVFÜGGETLEN: a tokenizálás Unicode \\w+ mintával történik,
    nincs benne semmilyen nyelvspecifikus szótár, stopszólista vagy
    szótövezés - így bármilyen nyelvű (nem csak magyar) szövegre azonos
    módon működik.
    """
    tokenek = re.findall(r'\w+', szoveg.lower(), re.UNICODE)
    if not tokenek:
        return 0

    sulyok = Counter(tokenek)
    vektor = [0] * hash_bitek
    for token, suly in sulyok.items():
        h = _stabil_hash64(token)
        for bit in range(hash_bitek):
            if h & (1 << bit):
                vektor[bit] += suly
            else:
                vektor[bit] -= suly

    ujjlenyomat = 0
    for bit in range(hash_bitek):
        if vektor[bit] > 0:
            ujjlenyomat |= (1 << bit)
    return ujjlenyomat


def simhash_hasonlosag(szoveg1: str, szoveg2: str, hash_bitek: int = 64) -> float:
    """Két szöveg Simhash-alapú hasonlósága (%) - gyors, nyelvfüggetlen."""
    if not szoveg1.strip() or not szoveg2.strip():
        return 0.0
    fp1 = simhash_ertek(szoveg1, hash_bitek)
    fp2 = simhash_ertek(szoveg2, hash_bitek)
    hamming_tavolsag = bin(fp1 ^ fp2).count("1")
    return max(0.0, (1 - hamming_tavolsag / hash_bitek)) * 100


# ============================================================================
# GYORS, DE PONTOSAN UGYANAZT SZÁMOLÓ KARAKTER-DIFF
# ----------------------------------------------------------------------------
# Ugyanazt az algoritmust (Ratcliff/Obershelp: leghosszabb közös blokk, majd
# rekurzió a két oldalán) és ugyanazt a holtverseny-szabályt használja, mint a
# difflib.SequenceMatcher(autojunk=False) - így az eredmény (százalék, egyező
# blokkok, opcode-ok) BITRE PONTOSAN azonos, csak a leghosszabb közös blokkot
# suffix-automatával keresi (közel lineáris idő a difflib négyzetes helyett).
# EZ AZ EGYETLEN hely, ahol a karakteres Diff-százalék számolódik: az Analysis
# mód, az Összesítő Tábla, a HTML riport és a Hierarchikus Diff is ezt hívja.
# ============================================================================

def _sam_epit(szoveg):
    nxt = [{}]
    link = [-1]
    hossz = [0]
    elso_veg = [-1]
    utolso = 0
    for idx, ch in enumerate(szoveg):
        cur = len(nxt)
        nxt.append({})
        hossz.append(hossz[utolso] + 1)
        link.append(0)
        elso_veg.append(idx)
        p = utolso
        while p != -1 and ch not in nxt[p]:
            nxt[p][ch] = cur
            p = link[p]
        if p == -1:
            link[cur] = 0
        else:
            q = nxt[p][ch]
            if hossz[p] + 1 == hossz[q]:
                link[cur] = q
            else:
                klon = len(nxt)
                nxt.append(dict(nxt[q]))
                hossz.append(hossz[p] + 1)
                link.append(link[q])
                elso_veg.append(elso_veg[q])
                while p != -1 and nxt[p].get(ch) == q:
                    nxt[p][ch] = klon
                    p = link[p]
                link[q] = klon
                link[cur] = klon
        utolso = cur
    return nxt, link, hossz, elso_veg


def _leghosszabb_egyezes(a, alo, ahi, b, blo, bhi):
    """Mint a difflib find_longest_match: leghosszabb blokk; holtversenyben a
    legkorábbi az a-ban, ezen belül a legkorábbi a b-ben. -> (i, j, hossz)"""
    a_bejar = (ahi - alo) >= (bhi - blo)   # a nagyobb tartományt járjuk be, a kisebbre építünk automatát
    if a_bejar:
        nxt, link, hossz, elso_veg = _sam_epit(b[blo:bhi])
        t, tlo, thi = a, alo, ahi
    else:
        nxt, link, hossz, elso_veg = _sam_epit(a[alo:ahi])
        t, tlo, thi = b, blo, bhi
    st = 0
    l = 0
    legjobb_k = 0
    legjobb = None
    for i in range(tlo, thi):
        ch = t[i]
        while st and ch not in nxt[st]:
            st = link[st]
            l = hossz[st]
        if ch in nxt[st]:
            st = nxt[st][ch]
            l += 1
        else:
            st = 0
            l = 0
        if l and l >= legjobb_k:
            t_kezd = i - l + 1
            s_kezd = elso_veg[st] - l + 1
            jel = (t_kezd, blo + s_kezd) if a_bejar else (alo + s_kezd, t_kezd)
            if l > legjobb_k:
                legjobb_k = l
                legjobb = jel
            elif jel < legjobb:
                legjobb = jel
    if not legjobb_k:
        return alo, blo, 0
    return legjobb[0], legjobb[1], legjobb_k


def karakter_egyezo_blokkok(a, b):
    """[(i, j, hossz), ...] növekvő sorrendben - azonos a
    difflib.SequenceMatcher(None, a, b, autojunk=False).get_matching_blocks()
    (záró 0 hosszú elem nélküli) eredményével."""
    verem = [(0, len(a), 0, len(b))]
    blokkok = []
    while verem:
        alo, ahi, blo, bhi = verem.pop()
        if alo >= ahi or blo >= bhi:
            continue
        i, j, k = _leghosszabb_egyezes(a, alo, ahi, b, blo, bhi)
        if k:
            blokkok.append((i, j, k))
            verem.append((alo, i, blo, j))
            verem.append((i + k, ahi, j + k, bhi))
    blokkok.sort()
    return blokkok


def karakter_diff_arany(a, b, blokkok=None):
    """Karakteres egyezési arány (%), azonos a difflib ratio()*100 értékével."""
    ossz = len(a) + len(b)
    if not ossz:
        return 100.0
    if blokkok is None:
        blokkok = karakter_egyezo_blokkok(a, b)
    return 2.0 * sum(k for _, _, k in blokkok) / ossz * 100


def karakter_diff_elemzes(a, b):
    """-> (opcode-ok, százalék); az opcode-ok azonosak a difflib get_opcodes() eredményével."""
    blokkok = karakter_egyezo_blokkok(a, b)
    opcodes = []
    i = j = 0
    for bi, bj, k in blokkok + [(len(a), len(b), 0)]:
        if i < bi and j < bj:
            opcodes.append(("replace", i, bi, j, bj))
        elif i < bi:
            opcodes.append(("delete", i, bi, j, bj))
        elif j < bj:
            opcodes.append(("insert", i, bi, j, bj))
        if k:
            opcodes.append(("equal", bi, bi + k, bj, bj + k))
        i, j = bi + k, bj + k
    return opcodes, karakter_diff_arany(a, b, blokkok)


# ============================================================================
# HIERARCHIKUS, TÖBBLÉPCSŐS ÖSSZEHASONLÍTÓ MOTOR
# ============================================================================

def karakter_profil(szoveg: str) -> dict:
    return {
        "total": len(szoveg),
        "letters": sum(1 for ch in szoveg if ch.isalpha()),
        "spaces": sum(1 for ch in szoveg if ch.isspace()),
        "digits": sum(1 for ch in szoveg if ch.isdigit()),
        "punctuation": sum(1 for ch in szoveg if ch in IRASJELEK),
        "frequency": Counter(szoveg),
    }


def karakterprofil_hasonlosag(profil_a: dict, profil_b: dict) -> float:
    a = profil_a["frequency"]
    b = profil_b["frequency"]
    kozos = sum((a & b).values())
    osszes = max(sum(a.values()), sum(b.values()), 1)
    return kozos / osszes * 100


def mondatok_tokenizalasa(szoveg: str) -> list:
    mondat_vege_re = re.compile(r"[.!?]+")
    mondatok = []
    last_end = 0
    for m in mondat_vege_re.finditer(szoveg):
        end = m.end()
        mondat_szoveg = szoveg[last_end:end].strip()
        if mondat_szoveg:
            szavak = []
            for token_m in re.finditer(r"\w+(?:[-'']\w+)*", mondat_szoveg, re.UNICODE):
                szavak.append({
                    "text": token_m.group(0),
                    "normalized": token_m.group(0).lower(),
                    "start": last_end + token_m.start(),
                    "end": last_end + token_m.end(),
                })
            mondatok.append({
                "text": mondat_szoveg,
                "start": last_end,
                "end": end,
                "tokens": szavak,
            })
        last_end = end
    maradek = szoveg[last_end:].strip()
    if maradek:
        szavak = []
        for token_m in re.finditer(r"\w+(?:[-'']\w+)*", maradek, re.UNICODE):
            szavak.append({
                "text": token_m.group(0),
                "normalized": token_m.group(0).lower(),
                "start": last_end + token_m.start(),
                "end": last_end + token_m.end(),
            })
        mondatok.append({
            "text": maradek,
            "start": last_end,
            "end": len(szoveg),
            "tokens": szavak,
        })
    return mondatok


def dokumentum_profil(szoveg: str) -> dict:
    sorok = szoveg.splitlines()
    mondatok = mondatok_tokenizalasa(szoveg)
    szavak = []
    for token_m in re.finditer(r"\w+(?:[-'']\w+)*", szoveg, re.UNICODE):
        szavak.append({
            "text": token_m.group(0),
            "normalized": token_m.group(0).lower(),
            "start": token_m.start(),
            "end": token_m.end(),
        })
    szoprofil = Counter(sz["normalized"] for sz in szavak)
    return {
        "text": szoveg,
        "lines": sorok,
        "sentences": mondatok,
        "words": szavak,
        "word_values": [sz["normalized"] for sz in szavak],
        "word_counter": szoprofil,
        "char_counter": Counter(szoveg),
        "char_profile": karakter_profil(szoveg),
        "stats": {
            "lines": len(sorok),
            "sentences": len(mondatok),
            "words": len(szavak),
            "characters": len(szoveg),
            "letters": sum(1 for ch in szoveg if ch.isalpha()),
            "spaces": sum(1 for ch in szoveg if ch.isspace()),
            "digits": sum(1 for ch in szoveg if ch.isdigit()),
            "punctuation": sum(1 for ch in szoveg if ch in IRASJELEK),
        },
    }


def normalizalt_mondat(mondat_szoveg: str) -> str:
    return " ".join(re.findall(r"\w+(?:[-'']\w+)*", mondat_szoveg.lower(), re.UNICODE))


def mondat_index(mondatok: list) -> dict:
    index = {}
    for sorszam, mondat in enumerate(mondatok):
        kulcs = normalizalt_mondat(mondat["text"])
        if kulcs:
            index.setdefault(kulcs, []).append(sorszam)
    return index


def mondat_egyezesi_terkep(profil_a: dict, profil_b: dict) -> dict:
    index_a = mondat_index(profil_a["sentences"])
    index_b = mondat_index(profil_b["sentences"])
    egyezik = []
    hasznalt_a = set()
    hasznalt_b = set()
    for kulcs in index_a.keys() & index_b.keys():
        poz_a = index_a[kulcs]
        poz_b = index_b[kulcs]
        for ia, ib in zip(poz_a, poz_b):
            if ia not in hasznalt_a and ib not in hasznalt_b:
                egyezik.append((ia, ib))
                hasznalt_a.add(ia)
                hasznalt_b.add(ib)
    eltero_a = [i for i in range(len(profil_a["sentences"])) if i not in hasznalt_a]
    eltero_b = [i for i in range(len(profil_b["sentences"])) if i not in hasznalt_b]
    return {"matches": egyezik, "unmatched_a": eltero_a, "unmatched_b": eltero_b}


def hierarchikus_diff(profil_a: dict, profil_b: dict, mondat_terkep: dict) -> dict:
    egyezo_mondat_a = {ia for ia, _ in mondat_terkep["matches"]}
    egyezo_mondat_b = {ib for _, ib in mondat_terkep["matches"]}
    maradek_a_reszletek = []
    maradek_b_reszletek = []
    for i, mondat in enumerate(profil_a["sentences"]):
        if i not in egyezo_mondat_a:
            maradek_a_reszletek.append((mondat["start"], mondat["end"], mondat["text"]))
    for i, mondat in enumerate(profil_b["sentences"]):
        if i not in egyezo_mondat_b:
            maradek_b_reszletek.append((mondat["start"], mondat["end"], mondat["text"]))
    maradek_a = "".join(t[2] for t in maradek_a_reszletek)
    maradek_b = "".join(t[2] for t in maradek_b_reszletek)
    if not maradek_a and not maradek_b:
        return {"blocks": [], "compared_characters_a": 0, "compared_characters_b": 0, "ratio": 100.0, "matching_characters": 0}
    blokkok = []
    for i1, j1, n in karakter_egyezo_blokkok(maradek_a, maradek_b):
        blokkok.append({"a_start": i1, "a_end": i1 + n, "b_start": j1, "b_end": j1 + n, "length": n})
    ratio = karakter_diff_arany(maradek_a, maradek_b, [(b["a_start"], b["b_start"], b["length"]) for b in blokkok])
    egyezo_karakter = sum(b["length"] for b in blokkok)
    return {"blocks": blokkok, "compared_characters_a": len(maradek_a), "compared_characters_b": len(maradek_b), "ratio": ratio, "matching_characters": egyezo_karakter}


def hierarchikus_egyezes(profil_a: dict, profil_b: dict, mondat_terkep: dict) -> dict:
    total_a = profil_a["stats"]["characters"]
    total_b = profil_b["stats"]["characters"]
    # Ugyanaz a normalizálás, mint a difflib ratio-nál: 2*M / (hossz_a + hossz_b).
    # (A korábbi M / max(hossz_a, hossz_b) hosszkülönbségnél szisztematikusan alacsonyabb értéket adott.)
    normalizalo = max((total_a + total_b) / 2.0, 1)
    azonos_mondat_karakterek = 0
    for ia, ib in mondat_terkep["matches"]:
        mondat_a = profil_a["sentences"][ia]
        mondat_b = profil_b["sentences"][ib]
        kozos = min(mondat_a["end"] - mondat_a["start"], mondat_b["end"] - mondat_b["start"])
        azonos_mondat_karakterek += kozos
    diff_eredmeny = hierarchikus_diff(profil_a, profil_b, mondat_terkep)
    maradek_egyezes = diff_eredmeny["matching_characters"]  # a ratio*len(a) NEM az egyező karakterek száma (ratio = 2M/(la+lb))
    osszes_egyezes = azonos_mondat_karakterek + maradek_egyezes
    return {
        "total_characters_a": total_a,
        "total_characters_b": total_b,
        "matching_characters": osszes_egyezes,
        "similarity": osszes_egyezes / normalizalo * 100,
        "sentence_matches": len(mondat_terkep["matches"]),
        "unmatched_sentences_a": len(mondat_terkep["unmatched_a"]),
        "unmatched_sentences_b": len(mondat_terkep["unmatched_b"]),
        "diff_ratio": diff_eredmeny["ratio"],
        "compared_characters_a": diff_eredmeny["compared_characters_a"],
        "compared_characters_b": diff_eredmeny["compared_characters_b"],
    }



def winnowing_hasonlosag(szoveg1: str, szoveg2: str, k: int = 4, w: int = 4) -> float:
    """
    A Winnowing ujjlenyomat-algoritmus önálló, modul szintű változata -
    megegyezik a SzTextCompar._winnowing_similarity logikájával, de itt
    azért létezik külön is, hogy a multiprocessing worker függvény
    (lásd lentebb) ne függjön a Tkinter-osztálytól.
    """
    def ujjlenyomatok(text):
        szavak = re.findall(r'\w+', text.lower())
        if len(szavak) < k:
            return set()
        ngramok = [tuple(szavak[i:i + k]) for i in range(len(szavak) - k + 1)]
        hasek = [_stabil_hash64(" ".join(ng)) for ng in ngramok]
        if not hasek:
            return set()
        fp = set()
        if len(hasek) < w:
            fp.add(min(hasek))
        else:
            for i in range(len(hasek) - w + 1):
                fp.add(min(hasek[i:i + w]))
        return fp

    fp1 = ujjlenyomatok(szoveg1)
    fp2 = ujjlenyomatok(szoveg2)
    if not fp1 or not fp2:
        return 0.0
    metszet = fp1 & fp2
    unio = fp1 | fp2
    return (len(metszet) / len(unio)) * 100 if unio else 0.0


def tfidf_cosine_hasonlosag(szoveg1: str, szoveg2: str, stopszavak=None) -> float:
    """A TF-IDF súlyozott koszinusz-hasonlóság önálló, modul szintű változata."""
    if stopszavak is None:
        stopszavak = stopszavak_a_szovegekhez(szoveg1, szoveg2)  # egyetlen igazság: mindenhol ugyanaz a szűrés
    w1 = [w for w in re.findall(r'\w+', szoveg1.lower()) if w not in stopszavak and len(w) > 1]
    w2 = [w for w in re.findall(r'\w+', szoveg2.lower()) if w not in stopszavak and len(w) > 1]
    if not w1 or not w2:
        return 0.0

    c1, c2 = Counter(w1), Counter(w2)
    vocab = set(c1) | set(c2)
    idf = {t: math.log(1.0 + (2.0 / ((1 if t in c1 else 0) + (1 if t in c2 else 0)))) for t in vocab}
    vec1 = {t: (c1[t] / len(w1)) * idf[t] for t in vocab}
    vec2 = {t: (c2[t] / len(w2)) * idf[t] for t in vocab}

    dot = sum(vec1[t] * vec2[t] for t in vocab)
    n1 = math.sqrt(sum(v ** 2 for v in vec1.values()))
    n2 = math.sqrt(sum(v ** 2 for v in vec2.values()))
    if not n1 or not n2:
        return 0.0
    return (dot / (n1 * n2)) * 100




# ---------------------------------------------------------------------------
# Gyorsítótárazás (caching) a mappa-mátrix vizsgálathoz.
# A kulcs a KÉT FÁJL TARTALMÁNAK sha256 hash-éből épül fel (nem a fájlnévből
# vagy útvonalból!), így ha egy fájlt átneveznek/áthelyeznek, de a tartalma
# nem változik, a korábban kiszámolt eredmény továbbra is felismerhető és
# újrafelhasználható - nem kell újraszámolni.
# ---------------------------------------------------------------------------

def _cache_fajl_utvonal() -> str:
    return str(Path.home() / ".sabtextcompar_cache.json")


def cache_betoltese() -> dict:
    utv = _cache_fajl_utvonal()
    if os.path.exists(utv):
        try:
            with open(utv, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}
    return {}


def cache_mentese(cache: dict) -> None:
    try:
        with open(_cache_fajl_utvonal(), "w", encoding="utf-8") as f:
            json.dump(cache, f)
    except Exception:
        pass  # A cache mentési hibája nem szabad, hogy megállítsa az alkalmazást.


def _tartalom_hash(szoveg: str) -> str:
    return hashlib.sha256(szoveg.encode("utf-8", errors="replace")).hexdigest()


def cache_kulcs(szoveg1: str, szoveg2: str) -> str:
    par = sorted([_tartalom_hash(szoveg1), _tartalom_hash(szoveg2)])
    return f"{CACHE_VERZIO}:{par[0]}:{par[1]}"


# ---------------------------------------------------------------------------
# Multiprocessing worker - modul szinten, hogy Windows/macOS "spawn" indítási
# módban is biztonságosan importálható és pickle-özhető legyen.
# ---------------------------------------------------------------------------

def _parvizsgalat_worker(adat):
    """
    Egy fájlpár teljes (CPU-intenzív) elemzése - ProcessPoolExecutor worker.
    adat: (f1nev, szoveg1, f2nev, szoveg2)
    visszater: (f1nev, f2nev, winnowing, tfidf, simhash)
    """
    f1nev, szoveg1, f2nev, szoveg2 = adat
    win = winnowing_hasonlosag(szoveg1, szoveg2)
    tfidf = tfidf_cosine_hasonlosag(szoveg1, szoveg2)
    simhash = simhash_hasonlosag(szoveg1, szoveg2)
    return (f1nev, f2nev, win, tfidf, simhash)


# ---------------------------------------------------------------------------
# HTML riport - a Python SZABVÁNYKÖNYVTÁR difflib.HtmlDiff eszközével épül
# (PSF licenc, a Python része - nem külső/szerzői jogvédett kód).
# ---------------------------------------------------------------------------

def _szoveg_ertekeles(szoveg1: str, szoveg2: str) -> list:
    """Kiszámolja az összes metrikát a HTML riport számára — a GUI-val konzisztens módon."""
    # Winnowing: a modul szintű stabil hash-t használó függvény (nem a Python hash())
    win = winnowing_hasonlosag(szoveg1, szoveg2)
    # TF-IDF: a szövegek nyelvének megfelelő stop-szavakkal (mint a GUI _tfidf_cosine_similarity)
    tfidf = tfidf_cosine_hasonlosag(szoveg1, szoveg2)
    simhash = simhash_hasonlosag(szoveg1, szoveg2)

    # Hierarchikus összehasonlítás
    try:
        profil_a = dokumentum_profil(szoveg1)
        profil_b = dokumentum_profil(szoveg2)
        mondat_terkep = mondat_egyezesi_terkep(profil_a, profil_b)
        hier_eredmeny = hierarchikus_egyezes(profil_a, profil_b, mondat_terkep)
        hier_szazalek = hier_eredmeny["similarity"]
        hier_leiras = f"Hierarchikus: {hier_eredmeny['sentence_matches']} egyező mondat, {hier_eredmeny['compared_characters_a']} karakteren Diff."
    except Exception:
        hier_szazalek = 0.0
        hier_leiras = "Hierarchikus összehasonlítás (nem elérhető)"

    # Szókészlet (Cosine): egyszerű Counter-alapú cosine IDF nélkül (mint a GUI _cosine_similarity)
    _sw = stopszavak_a_szovegekhez(szoveg1, szoveg2)
    words1 = [w for w in re.findall(r'\w+', szoveg1.lower()) if w not in _sw and len(w) > 1]
    words2 = [w for w in re.findall(r'\w+', szoveg2.lower()) if w not in _sw and len(w) > 1]
    if words1 and words2:
        v1 = Counter(words1)
        v2 = Counter(words2)
        intersection = set(v1.keys()) & set(v2.keys())
        numerator = sum(v1[x] * v2[x] for x in intersection)
        sum1 = sum(v ** 2 for v in v1.values())
        sum2 = sum(v ** 2 for v in v2.values())
        denominator = math.sqrt(sum1) * math.sqrt(sum2)
        cosine = float(numerator) / denominator * 100 if denominator else 0.0
    else:
        cosine = 0.0

    # Jaccard: egyedi szavak halmaz-átfedése (mint a GUI _jaccard_similarity)
    s1_set = set(re.findall(r'\w+', szoveg1.lower()))
    s2_set = set(re.findall(r'\w+', szoveg2.lower()))
    if not s1_set and not s2_set:
        jaccard = 100.0
    elif s1_set | s2_set:
        jaccard = (len(s1_set & s2_set) / len(s1_set | s2_set)) * 100
    else:
        jaccard = 0.0

    # N-gram: 4-szavas kifejezések (mint a GUI _get_ngrams)
    ng1 = set(tuple(re.findall(r'\w+', szoveg1.lower())[i:i+4]) for i in range(len(re.findall(r'\w+', szoveg1.lower())) - 3))
    ng2 = set(tuple(re.findall(r'\w+', szoveg2.lower())[i:i+4]) for i in range(len(re.findall(r'\w+', szoveg2.lower())) - 3))
    ngram = (len(ng1 & ng2) / len(ng1 | ng2)) * 100 if (ng1 and ng2 and (ng1 | ng2)) else 0.0

    # Diff: karakteres egyezés (mint a GUI SequenceMatcher)
    diff_szaz = karakter_diff_arany(szoveg1, szoveg2)

    # Ritmus: mondathossz-ritmus (mint a GUI _ritmus_elemzes)
    def _ritmus(t1, t2):
        l1 = [len(re.findall(r'\w+', s)) for s in re.split(r'[.!?]+', t1) if s.strip()]
        l2 = [len(re.findall(r'\w+', s)) for s in re.split(r'[.!?]+', t2) if s.strip()]
        if not l1 or not l2:
            return 0.0
        min_len = min(len(l1), len(l2))
        max_len = max(len(l1), len(l2))
        elteresek = sum(abs(l1[i] - l2[i]) for i in range(min_len))
        osszeg_max = sum(max(l1[i], l2[i]) for i in range(min_len)) if min_len > 0 else 1
        alap = max(0.0, (1.0 - (elteresek / max(1, osszeg_max))) * 100)
        hossz_buntetes = (min_len / max_len) * 100
        return (alap * 0.7) + (hossz_buntetes * 0.3)

    ritmus = _ritmus(szoveg1, szoveg2)

    return [
        ("Winnowing Ujjlenyomat", f"{win:.2f}%", "Átrendezésbiztos ujjlenyomat-alapú szövegegyezés-vizsgálat"),
        ("TF-IDF Súlyozott Tartalmi Elemzés", f"{tfidf:.2f}%", "Ritka szavak súlyozása alapú tematikus egyezés"),
        ("N-gram (4-szavas) Kifejezés", f"{ngram:.2f}%", "Közös fix 4-szavas kifejezések aránya"),
        ("Mondatritmus & Parafrázis", f"{ritmus:.2f}%", "Mondathossz ritmusprofil-egyezés"),
        ("Hagyományos Karakter Diff", f"{diff_szaz:.2f}%", "Közvetlen karakteres egyezési arány"),
        ("Szókészlet (Cosine)", f"{cosine:.2f}%", "Stop-szűrt szókészlet egyezése"),
        ("Jaccard Halmaz-hasonlóság", f"{jaccard:.2f}%", "Egyedi szavak halmaz-átfedése"),
        ("Simhash Ujjlenyomat", f"{simhash:.2f}%", "Nyelvfüggetlen Hamming-távolság alapú egyezés"),
        ("Hierarchikus Diff", f"{hier_szazalek:.2f}%", hier_leiras),

    ]


def _vizualis_egyezesi_blokkok(szoveg1: str, szoveg2: str, min_szavak: int = 5):
    """Pontos, helyhez kötött szövegegyezések keresése szavak alapján."""
    token_re = re.compile(r"\w+(?:[-’']\w+)*", re.UNICODE)
    def tokenize(text):
        return [(m.group(0).lower(), m.start(), m.end()) for m in token_re.finditer(text)]
    t1, t2 = tokenize(szoveg1), tokenize(szoveg2)
    if not t1 or not t2:
        return []
    a, b = [x[0] for x in t1], [x[0] for x in t2]
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    blokkok = []
    for i1, j1, n in sm.get_matching_blocks():
        if n < min_szavak:
            continue
        c1_start, c1_end = t1[i1][1], t1[i1+n-1][2]
        c2_start, c2_end = t2[j1][1], t2[j1+n-1][2]
        blokkok.append({"id": len(blokkok)+1, "words": n,
            "start1": c1_start, "end1": c1_end, "start2": c2_start, "end2": c2_end,
            "chars1": c1_end-c1_start, "chars2": c2_end-c2_start,
            "text1": szoveg1[c1_start:c1_end], "text2": szoveg2[c2_start:c2_end]})
    osszevont=[]
    for bl in blokkok:
        if osszevont:
            elo=osszevont[-1]
            if len(szoveg1[elo["end1"]:bl["start1"]].strip())<=8 and len(szoveg2[elo["end2"]:bl["start2"]].strip())<=8:
                elo["end1"], elo["end2"] = bl["end1"], bl["end2"]
                elo["words"] += bl["words"]
                elo["chars1"], elo["chars2"] = elo["end1"]-elo["start1"], elo["end2"]-elo["start2"]
                elo["text1"], elo["text2"] = szoveg1[elo["start1"]:elo["end1"]], szoveg2[elo["start2"]:elo["end2"]]
                continue
        osszevont.append(dict(bl))
    for i, bl in enumerate(osszevont, 1): bl["id"] = i
    return osszevont


def _ngram_egyezesi_blokkok(szoveg1: str, szoveg2: str, n: int = 4):
    """Közös, helyhez kötött N-szavas kifejezések blokkjai a főablaki kiemeléshez."""
    token_re = re.compile(r"\w+(?:[-’']\w+)*", re.UNICODE)
    t1 = [(m.group(0).lower(), m.start(), m.end()) for m in token_re.finditer(szoveg1)]
    t2 = [(m.group(0).lower(), m.start(), m.end()) for m in token_re.finditer(szoveg2)]
    if len(t1) < n or len(t2) < n:
        return []

    def elofordulasok(tokenek):
        eredmeny = {}
        for i in range(len(tokenek) - n + 1):
            eredmeny.setdefault(tuple(x[0] for x in tokenek[i:i+n]), []).append(i)
        return eredmeny

    p1, p2 = elofordulasok(t1), elofordulasok(t2)
    parok = []
    for ngram in p1.keys() & p2.keys():
        # Ismétlődő kifejezéseknél a sorrend szerinti párosítás átlátható,
        # és elkerüli az összes lehetséges keresztszorzatot.
        for i, j in zip(p1[ngram], p2[ngram]):
            parok.append((i, j))
    parok.sort()

    blokkok = []
    for i, j in parok:
        if blokkok and i <= blokkok[-1]["i_vege"] and j <= blokkok[-1]["j_vege"]:
            continue  # átfedő N-gram, már az előző blokk része
        if blokkok and i == blokkok[-1]["i_vege"] and j == blokkok[-1]["j_vege"]:
            blokk = blokkok[-1]
            blokk["i_vege"] = i + n
            blokk["j_vege"] = j + n
            blokk["end1"] = t1[i+n-1][2]
            blokk["end2"] = t2[j+n-1][2]
            blokk["words"] = blokk["i_vege"] - blokk["i_kezd"]
            blokk["chars1"] = blokk["end1"] - blokk["start1"]
            blokk["chars2"] = blokk["end2"] - blokk["start2"]
            blokk["text1"] = szoveg1[blokk["start1"]:blokk["end1"]]
            blokk["text2"] = szoveg2[blokk["start2"]:blokk["end2"]]
            continue
        blokkok.append({
            "i_kezd": i, "i_vege": i+n, "j_kezd": j, "j_vege": j+n,
            "words": n, "start1": t1[i][1], "end1": t1[i+n-1][2],
            "start2": t2[j][1], "end2": t2[j+n-1][2],
            "chars1": t1[i+n-1][2] - t1[i][1], "chars2": t2[j+n-1][2] - t2[j][1],
            "text1": szoveg1[t1[i][1]:t1[i+n-1][2]],
            "text2": szoveg2[t2[j][1]:t2[j+n-1][2]],
        })
    for azonosito, blokk in enumerate(blokkok, 1):
        blokk["id"] = azonosito
        blokk.pop("i_kezd"); blokk.pop("i_vege"); blokk.pop("j_kezd"); blokk.pop("j_vege")
    return blokkok


def _offset_to_tk_index(text: str, offset: int) -> str:
    before=text[:offset]
    line=before.count("\n")+1
    last_nl=before.rfind("\n")
    col=offset if last_nl<0 else offset-last_nl-1
    return f"{line}.{col}"


def html_riport_generalasa(cimke1: str, szoveg1: str, cimke2: str, szoveg2: str, cel_utvonal: str) -> None:
    metrikak=_szoveg_ertekeles(szoveg1,szoveg2)
    osszesitett=float(metrikak[0][1].replace('%',''))*.35+float(metrikak[1][1].replace('%',''))*.25+float(metrikak[2][1].replace('%',''))*.20+float(metrikak[4][1].replace('%',''))*.10+float(metrikak[3][1].replace('%',''))*.10
    if osszesitett<15: minosites,szin="Alacsony / Csekély szöveghasonlóság","#006600"
    elif osszesitett<35: minosites,szin="Mérsékelt / Hasonló téma vagy részbeni átfedés","#b37700"
    else: minosites,szin="MAGAS / ERŐS SZÖVEGEGYEZÉS","#cc0000"
    blokkok=_vizualis_egyezesi_blokkok(szoveg1,szoveg2,5)
    rows=''.join(f"<tr><td>{html.escape(tr(n))}</td><td class='ertek'>{html.escape(v)}</td><td>{html.escape(tr(d))}</td></tr>" for n,v,d in metrikak)
    def render_doc(text,side):
        spans=sorted((b["start1" if side==1 else "start2"],b["end1" if side==1 else "end2"],b["id"]) for b in blokkok); out=[]; pos=0
        for a,b,mid in spans:
            if a<pos: continue
            out.append(html.escape(text[pos:a])); out.append(f'<mark class="m m{mid}" data-match="{mid}">{html.escape(text[a:b])} <sup>#{mid}</sup></mark>'); pos=b
        out.append(html.escape(text[pos:])); return ''.join(out).replace('\n','<br>')
    lista=''.join(f'<div class="match-row" data-match="{b["id"]}"><b>#{b["id"]}</b> <span>{b["words"]} {tr("szó")}</span> — <span>{html.escape(re.sub(r"\s+"," ",b["text1"]).strip()[:180])}</span></div>' for b in blokkok) or f'<div class="empty">{tr("Nem találtam legalább 5 egymást követő azonos szót tartalmazó szakaszt.")}</div>'
    doc=f'''<!doctype html><html lang="{CURRENT_LANGUAGE}"><head><meta charset="utf-8"><title>{html.escape(tr("SzTextCompar — vizuális egyezési riport"))}</title><style>
body{{font-family:Arial,sans-serif;margin:20px;background:#f5f6f8;color:#222}} h1{{margin-bottom:6px}} .note{{color:#555}} .metrics{{background:#fff;border:1px solid #ccc;border-radius:10px;padding:16px;margin:16px 0}} table{{border-collapse:collapse;width:100%}} th,td{{border:1px solid #ddd;padding:7px}} th{{background:#333;color:#fff;text-align:left}} td.ertek{{text-align:center;font-weight:bold}} .summary{{margin-top:12px;padding:12px;border-left:6px solid {szin};background:#fafafa;font-weight:bold}} .legend{{display:flex;gap:18px;flex-wrap:wrap;margin:12px 0}} .legend span{{padding:5px 9px;border-radius:5px;border:1px solid #ccc}} .exact{{background:#d9f2d9}} .match-list{{background:#fff;border:1px solid #ccc;border-radius:10px;padding:12px;margin:16px 0;max-height:260px;overflow:auto}} .match-row{{padding:8px;border-bottom:1px solid #eee;cursor:pointer}} .match-row:hover{{background:#fff0b3}} .compare{{display:grid;grid-template-columns:1fr 1fr;gap:12px;align-items:start}} .pane{{background:#fff;border:1px solid #bbb;border-radius:8px;overflow:auto;max-height:70vh}} .pane h2{{position:sticky;top:0;background:#333;color:#fff;margin:0;padding:9px;font-size:15px;z-index:2}} .text{{padding:14px;font-family:Consolas,monospace;line-height:1.5;word-wrap:break-word}} mark{{padding:1px 2px;border-radius:3px;cursor:pointer;background:#d9f2d9}} mark sup{{font-size:9px;color:#555}} .active{{outline:2px solid #ff9800;background:#ffcc66!important}} @media(max-width:900px){{.compare{{grid-template-columns:1fr}}}}
</style></head><body><h1>{tr("🔎 SzTextCompar — vizuális egyezési riport")}</h1><div class="note">{tr("A pontos egyezések azonos sorszámot (#) kapnak mindkét oldalon. Ez az egyezés helyét mutatja; önmagában nem bizonyít másolást vagy szerzői jogsértést.")}</div><div class="metrics"><h2>{tr("📊 Metrikák")}</h2><table><tr><th>{tr("Vizsgálati módszer")}</th><th>{tr("Mért érték")}</th><th>{tr("Leírás")}</th></tr>{rows}</table><div class="summary">{tr("🎯 Súlyozott összesített szöveghasonlósági index:")} {osszesitett:.2f}% — {html.escape(tr(minosites))}</div></div><div class="legend"><span class="exact">{tr("🟩 Pontos szövegegyezés")}</span><span>{tr("🔢 Azonos # = ugyanaz a szakasz")}</span></div><div class="match-list"><h2>{tr("📌 Egyezési szakaszok")} ({len(blokkok)})</h2>{lista}</div><div class="compare"><section class="pane"><h2>{html.escape(cimke1)}</h2><div class="text">{render_doc(szoveg1,1)}</div></section><section class="pane"><h2>{html.escape(cimke2)}</h2><div class="text">{render_doc(szoveg2,2)}</div></section></div><script>
function activate(id){{document.querySelectorAll('.active').forEach(e=>e.classList.remove('active'));document.querySelectorAll('[data-match="'+id+'"]').forEach(e=>{{e.classList.add('active');e.scrollIntoView({{behavior:'smooth',block:'center'}});}})}} document.querySelectorAll('[data-match]').forEach(e=>e.addEventListener('click',()=>activate(e.dataset.match)));
</script></body></html>'''
    with open(cel_utvonal,'w',encoding='utf-8') as f: f.write(doc)


# ---------------------------------------------------------------------------
# Egyszerű, függőségmentes sávdiagram tiszta Tkinter Canvas-szal.
# (Nincs matplotlib-függőség; csak alap Canvas-primitíveket használ, tehát
# szerzői jogi aggály sincs, hiszen ez nem "mű", hanem néhány sor rajzoló
# kód, ami bármely Tkinter-alkalmazásban szabadon, azonos módon íródik meg.)
# ---------------------------------------------------------------------------

def sav_diagram_rajzolasa(canvas: tk.Canvas, adatok) -> None:
    """adatok: [(cimke:str, ertek_szazalek:float), ...]"""
    canvas.delete("all")
    canvas.update_idletasks()
    szelesseg = canvas.winfo_width() or 780
    magassag = canvas.winfo_height() or 320
    if not adatok:
        return

    bal_margo = 230
    also_margo = 20
    felso_margo = 20
    sav_terulet = max(50, szelesseg - bal_margo - 60)
    n = len(adatok)
    sor_magassag = (magassag - felso_margo - also_margo) / n
    sav_magassag = max(12, sor_magassag - 8)

    canvas.create_line(bal_margo, felso_margo, bal_margo, magassag - also_margo, fill="#999999")
    for x_szaz in (0, 25, 50, 75, 100):
        x = bal_margo + (x_szaz / 100.0) * sav_terulet
        canvas.create_line(x, felso_margo, x, magassag - also_margo, fill="#eeeeee")
        canvas.create_text(x, magassag - also_margo + 10, text=f"{x_szaz}%", font=("TkDefaultFont", 7), fill="#999999")

    for i, (cimke, ertek) in enumerate(adatok):
        ertek = max(0.0, min(100.0, ertek))
        y = felso_margo + i * sor_magassag + (sor_magassag - sav_magassag) / 2
        hossz = (ertek / 100.0) * sav_terulet
        szin = "#cc3333" if ertek >= 40 else ("#cc8800" if ertek >= 15 else "#2e7d32")
        canvas.create_rectangle(bal_margo, y, bal_margo + hossz, y + sav_magassag, fill=szin, outline="")
        canvas.create_text(bal_margo - 8, y + sav_magassag / 2, text=cimke, anchor="e", font=("TkDefaultFont", 8))
        canvas.create_text(bal_margo + hossz + 6, y + sav_magassag / 2, text=f"{ertek:.1f}%",
                            anchor="w", font=("TkDefaultFont", 8, "bold"))

# ---------------------------------------------------------------------------
# "Részletes vizualizáció" ablak -> önálló HTML fájlba mentése.
# Ugyanazt a kék/narancs színkódot (#3976b9 / #e4873a) és elrendezést követi,
# mint a Tkinter Canvas-alapú grafikonok, csak függőségmentes, beágyazott
# SVG-ként, hogy a riport egyetlen, böngészőben önmagában megnyitható
# HTML fájl legyen (nincs matplotlib vagy egyéb külső csomag-függőség).
# ---------------------------------------------------------------------------

def _svg_ketsoros_oszlopdiagram(adatok, bal_nev: str, jobb_nev: str, szelesseg: int = 820, magassag: int = 320) -> str:
    """adatok: [(cimke, bal_ertek, jobb_ertek), ...] -> önálló SVG karakterlánc."""
    if not adatok:
        return (f'<svg viewBox="0 0 {szelesseg} {magassag}" xmlns="http://www.w3.org/2000/svg">'
                 f'<text x="{szelesseg/2}" y="{magassag/2}" text-anchor="middle" fill="#666">{html.escape(tr("Nincs adat."))}</text></svg>')
    bal_margo, jobb_margo, felso, also = 70, 25, 66, 70
    diagram_mag = max(1, magassag - felso - also)
    maximum = max(1.0, max(max(float(a[1]), float(a[2])) for a in adatok))
    csoport = (szelesseg - bal_margo - jobb_margo) / len(adatok)
    oszlop = min(40, csoport * 0.30)
    r = [f'<svg viewBox="0 0 {szelesseg} {magassag}" xmlns="http://www.w3.org/2000/svg" '
         f'font-family="Arial,sans-serif" font-size="11">']
    r.append(f'<rect x="{bal_margo}" y="{felso}" width="{szelesseg-bal_margo-jobb_margo}" '
              f'height="{diagram_mag}" fill="none" stroke="#b0b0b0"/>')
    for i in range(5):
        y = felso + diagram_mag * i / 4
        ertek = maximum * (1 - i / 4)
        r.append(f'<line x1="{bal_margo}" y1="{y:.1f}" x2="{szelesseg-jobb_margo}" y2="{y:.1f}" stroke="#e5e5e5"/>')
        r.append(f'<text x="{bal_margo-7}" y="{y+3:.1f}" text-anchor="end" fill="#555">{ertek:.0f}</text>')
    for i, (cimke, bv, jv) in enumerate(adatok):
        bv, jv = float(bv), float(jv)
        kozep = bal_margo + csoport * (i + .5)
        for x, ertek, szin in ((kozep - oszlop - 2, bv, "#3976b9"), (kozep + 2, jv, "#e4873a")):
            y = magassag - also - (ertek / maximum * diagram_mag)
            h = magassag - also - y
            r.append(f'<rect x="{x:.1f}" y="{y:.1f}" width="{oszlop:.1f}" height="{max(0.0,h):.1f}" fill="{szin}"/>')
            r.append(f'<text x="{x+oszlop/2:.1f}" y="{y-6:.1f}" text-anchor="middle" font-size="9">{ertek:.1f}</text>')
        cimke_r = html.escape(str(cimke))
        if len(cimke_r) > 16:
            cimke_r = cimke_r[:15] + "…"
        r.append(f'<text x="{kozep:.1f}" y="{magassag-also+16:.1f}" text-anchor="middle">{cimke_r}</text>')
    bal_nev_r = html.escape(bal_nev)
    jobb_nev_r = html.escape(jobb_nev)
    r.append(f'<rect x="{bal_margo}" y="8" width="14" height="14" fill="#3976b9"/>'
              f'<text x="{bal_margo+20}" y="19">{bal_nev_r}<title>{bal_nev_r}</title></text>')
    r.append(f'<rect x="{bal_margo}" y="34" width="14" height="14" fill="#e4873a"/>'
              f'<text x="{bal_margo+20}" y="45">{jobb_nev_r}<title>{jobb_nev_r}</title></text>')
    r.append('</svg>')
    return ''.join(r)


def _svg_vonaldiagram(bal_adatok, jobb_adatok, bal_nev: str, jobb_nev: str, szelesseg: int = 820, magassag: int = 300) -> str:
    """Mondathosszak kétvonalas grafikonja, önálló SVG-ként."""
    if not bal_adatok or not jobb_adatok:
        return (f'<svg viewBox="0 0 {szelesseg} {magassag}" xmlns="http://www.w3.org/2000/svg">'
                 f'<text x="{szelesseg/2}" y="{magassag/2}" text-anchor="middle" fill="#666">'
                 f'{html.escape(tr("Nincs elég adat."))}</text></svg>')
    bal_margo, jobb_margo, felso, also = 55, 25, 60, 50
    diagram_mag = magassag - felso - also
    diagram_szel = szelesseg - bal_margo - jobb_margo
    szam = max(len(bal_adatok), len(jobb_adatok))
    maximum = max(1, max(list(bal_adatok) + list(jobb_adatok)))
    r = [f'<svg viewBox="0 0 {szelesseg} {magassag}" xmlns="http://www.w3.org/2000/svg" '
         f'font-family="Arial,sans-serif" font-size="11">']
    r.append(f'<rect x="{bal_margo}" y="{felso}" width="{diagram_szel}" height="{diagram_mag}" fill="none" stroke="#b0b0b0"/>')
    for i in range(5):
        y = felso + diagram_mag * i / 4
        r.append(f'<line x1="{bal_margo}" y1="{y:.1f}" x2="{szelesseg-jobb_margo}" y2="{y:.1f}" stroke="#e5e5e5"/>')
        r.append(f'<text x="{bal_margo-7}" y="{y+3:.1f}" text-anchor="end" fill="#555">{maximum*(1-i/4):.0f}</text>')

    def pontok(adatok):
        return [(bal_margo + diagram_szel * i / max(1, szam - 1),
                  magassag - also - diagram_mag * ertek / maximum) for i, ertek in enumerate(adatok)]

    for adatok, szin in ((bal_adatok, "#3976b9"), (jobb_adatok, "#e4873a")):
        p = pontok(adatok)
        if len(p) == 1:
            x, y = p[0]
            r.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3" fill="{szin}"/>')
        else:
            pts = ' '.join(f'{x:.1f},{y:.1f}' for x, y in p)
            r.append(f'<polyline points="{pts}" fill="none" stroke="{szin}" stroke-width="2"/>')
            for x, y in p:
                r.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="2.6" fill="{szin}"/>')
    kozep_x = (bal_margo + szelesseg - jobb_margo) / 2
    kozep_y = (felso + magassag - also) / 2
    r.append(f'<text x="{kozep_x:.1f}" y="{magassag-16}" text-anchor="middle">{html.escape(tr("Mondat sorszáma"))}</text>')
    r.append(f'<text x="14" y="{kozep_y:.1f}" text-anchor="middle" transform="rotate(-90 14,{kozep_y:.1f})">{html.escape(tr("Szó"))}</text>')
    r.append(f'<line x1="{bal_margo}" y1="15" x2="{bal_margo+18}" y2="15" stroke="#3976b9" stroke-width="3"/>'
              f'<text x="{bal_margo+24}" y="19">{html.escape(bal_nev)}<title>{html.escape(bal_nev)}</title></text>')
    r.append(f'<line x1="{bal_margo}" y1="37" x2="{bal_margo+18}" y2="37" stroke="#e4873a" stroke-width="3"/>'
              f'<text x="{bal_margo+24}" y="41">{html.escape(jobb_nev)}<title>{html.escape(jobb_nev)}</title></text>')
    r.append('</svg>')
    return ''.join(r)


def reszletes_vizualizacio_html_riport_generalasa(cimke1: str, cimke2: str, kulcs_adat, ritmus: float,
                                                    hossz1, hossz2, stil_adat, kozos_ngramok,
                                                    rendezett1, rendezett2, cel_utvonal: str) -> None:
    """A "Részletes vizualizáció" ablak (Kulcsszavak / Mondatritmus / Stilisztika /
    Közös N-gramok / Szógyakoriság) teljes tartalmát egyetlen, önmagában
    megnyitható HTML fájlba menti - ugyanazokkal a grafikonokkal és
    táblázatokkal, mint amit az alkalmazás ablakában lát a felhasználó."""
    kulcs_svg = _svg_ketsoros_oszlopdiagram(kulcs_adat, cimke1, cimke2)
    stil_svg = _svg_ketsoros_oszlopdiagram(stil_adat, cimke1, cimke2)
    ritmus_svg = _svg_vonaldiagram(hossz1, hossz2, cimke1, cimke2)

    kulcs_rows = ''.join(
        f'<tr><td>{html.escape(str(szo))}</td><td class="ertek">{bal}</td><td class="ertek">{jobb}</td></tr>'
        for szo, bal, jobb in kulcs_adat
    ) or f'<tr><td colspan="3" class="empty">{html.escape(tr("Nincs adat."))}</td></tr>'

    stil_rows = ''.join(
        f'<tr><td>{html.escape(str(cimke))}</td><td class="ertek">{float(bv):.2f}</td><td class="ertek">{float(jv):.2f}</td></tr>'
        for cimke, bv, jv in stil_adat
    )

    ngram_items = ''.join(f'<li>{html.escape(ng)}</li>' for ng in kozos_ngramok) \
        or f'<li class="empty">{html.escape(tr("Nincs közös 4-szavas kifejezés."))}</li>'

    freq_rows_lista = []
    for i in range(max(len(rendezett1), len(rendezett2))):
        bsz, bdb = rendezett1[i] if i < len(rendezett1) else ("", "")
        jsz, jdb = rendezett2[i] if i < len(rendezett2) else ("", "")
        freq_rows_lista.append(
            f'<tr><td>{html.escape(str(bsz))}</td><td class="ertek">{bdb}</td>'
            f'<td>{html.escape(str(jsz))}</td><td class="ertek">{jdb}</td></tr>'
        )
    freq_rows = ''.join(freq_rows_lista)

    osszeg1 = sum(db for _, db in rendezett1)
    osszeg2 = sum(db for _, db in rendezett2)

    cimke1_e, cimke2_e = html.escape(cimke1), html.escape(cimke2)

    doc = f'''<!doctype html><html lang="{CURRENT_LANGUAGE}"><head><meta charset="utf-8">
<title>{html.escape(tr("SzTextCompar — Részletes vizualizáció riport"))}</title>
<style>
body{{font-family:Arial,sans-serif;margin:20px;background:#f5f6f8;color:#222}}
h1{{margin-bottom:6px}}
h2{{margin:0;padding:10px 14px;background:#333;color:#fff;border-radius:8px 8px 0 0;font-size:15px}}
.note{{color:#555;margin-bottom:16px;font-weight:bold}}
.card{{background:#fff;border:1px solid #ccc;border-radius:10px;margin:18px 0;overflow:hidden}}
.card-body{{padding:14px}}
table{{border-collapse:collapse;width:100%;margin-top:10px}}
th,td{{border:1px solid #ddd;padding:6px 8px;text-align:left;font-size:13px}}
th{{background:#eef1f5}}
td.ertek{{text-align:center;font-weight:bold}}
svg{{width:100%;height:auto;display:block;background:#fff}}
ul.ngram{{columns:3;-webkit-columns:3;column-gap:20px;list-style:none;padding:0;margin:10px 0;font-family:Consolas,monospace;font-size:12.5px}}
ul.ngram li{{padding:3px 0;border-bottom:1px solid #f0f0f0;break-inside:avoid}}
.empty{{color:#888;font-style:italic}}
.meta{{color:#555;font-size:13px;margin-bottom:6px}}
@media(max-width:800px){{ul.ngram{{columns:1}}}}
</style></head><body>
<h1>{html.escape(tr("📊 SzTextCompar — Részletes vizualizáció riport"))}</h1>
<div class="note">{cimke1_e} &nbsp;⇄&nbsp; {cimke2_e}</div>

<div class="card"><h2>{html.escape(tr("  Kulcsszavak  ").strip())}</h2><div class="card-body">
<p class="meta">{html.escape(tr("A stop-szavak nélküli, mindkét szövegben előforduló legerősebb kulcsszavak."))}</p>
{kulcs_svg}
<table><tr><th>{html.escape(tr("Szó"))}</th><th>{cimke1_e}</th><th>{cimke2_e}</th></tr>{kulcs_rows}</table>
</div></div>

<div class="card"><h2>{html.escape(tr("  Mondatritmus  ").strip())}</h2><div class="card-body">
<p class="meta">{html.escape(tr(f"Mondatritmus-egyezés: {ritmus:.2f}%. A vonalak a mondatok szavainak számát mutatják."))}</p>
{ritmus_svg}
</div></div>

<div class="card"><h2>{html.escape(tr("  Stilisztika  ").strip())}</h2><div class="card-body">
<p class="meta">{html.escape(tr("A nyers stilisztikai mutatók összehasonlítása (eltérő mértékegységek miatt elsősorban arányként értelmezendő)."))}</p>
{stil_svg}
<table><tr><th>{html.escape(tr("Mutató"))}</th><th>{cimke1_e}</th><th>{cimke2_e}</th></tr>{stil_rows}</table>
</div></div>

<div class="card"><h2>{html.escape(tr("  Közös N-gramok  ").strip())}</h2><div class="card-body">
<p class="meta">{html.escape(tr(f"Közös, egymást követő 4-szavas kifejezések: {len(kozos_ngramok)} db."))}</p>
<ul class="ngram">{ngram_items}</ul>
</div></div>

<div class="card"><h2>{html.escape(tr("  Szógyakoriság  ").strip())}</h2><div class="card-body">
<p class="meta">{html.escape(tr(f"Minden szó kisbetűsítve szerepel; mindkét lista külön a leggyakoribb szóval kezdődik.  "
                  f"Bal: {osszeg1} szó, {len(rendezett1)} egyedi.  "
                  f"Jobb: {osszeg2} szó, {len(rendezett2)} egyedi."))}</p>
<table><tr><th>{html.escape(tr("Bal fájl – szó"))}</th><th>{html.escape(tr("Db"))}</th>
<th>{html.escape(tr("Jobb fájl – szó"))}</th><th>{html.escape(tr("Db"))}</th></tr>{freq_rows}</table>
</div></div>

</body></html>'''
    with open(cel_utvonal, 'w', encoding='utf-8') as f:
        f.write(doc)


MAGYAR_STOPSZAVAK = {
    "a", "az", "egy", "hogy", "is", "nem", "de", "és", "vagy", "mint", "ez", "azt", 
    "ha", "csak", "már", "volt", "van", "lesz", "meg", "még", "kell", "lehet", 
    "volna", "sok", "minden", "aki", "aminek", "amely", "azok", "ezek", "mi", "ki", 
    "te", "ő", "ti", "ők", "nekem", "neked", "neki", "nekünk", "nektek", "nekik", 
    "abban", "ahhoz", "ebből", "annak", "ezzel", "azzal", "ott", "itt", "ezt", "pedig", 
    "sőt", "se", "sem", "stb", "által", "után", "szerint", "alatt", "felett", "mellett", 
    "között", "nélkül", "miatt", "miért", "hogyan", "mikor", "mely", "melyik", "hogy", "mert"
}

# Az angol párja: a leggyakoribb angol funkciószavak (névelők, névmások, segédigék,
# elöljárók, kötőszavak). Saját összeállítású, rövid lista - ténybeli adat, nem külső kód.
ANGOL_STOPSZAVAK = {
    "a", "an", "the", "and", "or", "but", "if", "of", "at", "by", "for", "with", "about", "against",
    "between", "into", "through", "during", "before", "after", "above", "below", "to", "from", "up",
    "down", "in", "out", "on", "off", "over", "under", "again", "further", "then", "once", "here",
    "there", "when", "where", "why", "how", "all", "any", "both", "each", "few", "more", "most",
    "other", "some", "such", "no", "nor", "not", "only", "own", "same", "so", "than", "too", "very",
    "can", "will", "just", "should", "now", "is", "are", "was", "were", "be", "been", "being", "have",
    "has", "had", "having", "do", "does", "did", "doing", "i", "me", "my", "myself", "we", "our",
    "ours", "you", "your", "yours", "he", "him", "his", "she", "her", "hers", "it", "its", "they",
    "them", "their", "theirs", "what", "which", "who", "whom", "this", "that", "these", "those", "am",
    "would", "could", "shall", "may", "might", "must", "as", "while", "because", "until", "also",
    "upon", "within", "without", "among", "s", "t",
}
_STOP_CACHE = {}


def _szoveg_nyelve(szoveg: str):
    """'hu', 'en' vagy None (nem egyértelmű) a leggyakoribb funkciószavak alapján.
    A mindkét listában azonos alakú szavakat (pl. „a”, „is”) nem számolja."""
    kulcs = hash(szoveg[:200000])
    if kulcs in _STOP_CACHE:
        return _STOP_CACHE[kulcs]
    szavak = re.findall(r"\w+", szoveg[:200000].lower())
    csak_hu = MAGYAR_STOPSZAVAK - ANGOL_STOPSZAVAK
    csak_en = ANGOL_STOPSZAVAK - MAGYAR_STOPSZAVAK
    hu = sum(1 for w in szavak if w in csak_hu)
    en = sum(1 for w in szavak if w in csak_en)
    if en > 1.5 * hu and en > 0:
        nyelv = "en"
    elif hu > 1.5 * en and hu > 0:
        nyelv = "hu"
    else:
        nyelv = None
    if len(_STOP_CACHE) > 128:
        _STOP_CACHE.clear()
    _STOP_CACHE[kulcs] = nyelv
    return nyelv


def stopszavak_a_szovegekhez(szoveg1: str, szoveg2: str):
    """Kiválasztja a szövegek nyelvének megfelelő stopszólistát (magyar / angol).

    Mindkét szöveg nyelvét külön felismeri: ha mindkettő magyar, a magyar, ha mindkettő
    angol, az angol listát használja; ha a nyelv nem egyértelmű vagy a két szöveg nyelve
    eltér (pl. fordítás összevetése), a két lista egyesítését. A döntés csak a szövegektől
    függ, a program felületi nyelvétől nem."""
    nyelvek = {_szoveg_nyelve(szoveg1), _szoveg_nyelve(szoveg2)}
    if nyelvek == {"en"}:
        return ANGOL_STOPSZAVAK
    if nyelvek == {"hu"}:
        return MAGYAR_STOPSZAVAK
    return MAGYAR_STOPSZAVAK | ANGOL_STOPSZAVAK


IDOBELYEG_SOR = re.compile(
    r'^\s*\d{1,2}:\d{2}:\d{2}[.,]\d{3}\s*-->\s*\d{1,2}:\d{2}:\d{2}[.,]\d{3}.*$',
    re.MULTILINE
)
IDOBELYEG_INLINE = re.compile(r'<\d{1,2}:\d{2}:\d{2}[.,]\d{3}>')
SORSZAM_SOR = re.compile(r'^\s*\d+\s*$', re.MULTILINE)
WEBVTT_FEJLEC = re.compile(r'^\s*WEBVTT.*$', re.MULTILINE)


# ============================================================================
# TELJES KÉPERNYŐS EKG-NÉZET
# ----------------------------------------------------------------------------
# Két szöveg egymás mellett + alul egy EKG-szerű "egyezési hullám":
#   - nincs egyezés            -> egyenes vonal
#   - 1 szó egyezik            -> kis csúcs, 2 szó -> magasabb, stb.
#   - egy egész mondat (vagy EKG_TELJES_SZO szavas / hosszabb szakasz) -> teljes
#     magasságú csúcs; hosszú, egymás után következő 100%-os egyezésnél a vonal
#     a maximumon marad (a szélessége arányos a teljes diagram hosszával)
# Kattintás / húzás a hullámon: mindkét szövegpanel egyszerre odaugrik.
# Nagyítás csak vízszintesen (hosszában): görgő = nagyítás, jobb gomb húzása
# vagy a görgetősáv = eltolás.
# ============================================================================

EKG_TELJES_SZO = 8      # ennyi szavas (vagy hosszabb) egyezés = teljes csúcs
EKG_MIN_MONDAT = 3      # legalább ennyi szavas, teljesen egyező mondat = teljes csúcs
EKG_KOTOPONT_MIN = 3    # a szinkron-térképhez használt legrövidebb egyezés (szó)

_EKG_SZO_RE = re.compile(r"\w+(?:[-’']\w+)*", re.UNICODE)


def _ekg_szavak(szoveg):
    szavak, kezdetek, vegek = [], [], []
    for m in _EKG_SZO_RE.finditer(szoveg):
        szavak.append(m.group(0).lower())
        kezdetek.append(m.start())
        vegek.append(m.end())
    return szavak, kezdetek, vegek


def ekg_adatok_szamitasa(szoveg1, szoveg2):
    """Szó szintű egyezések a két szöveg között (háttérszálból is hívható)."""
    sz1, k1, v1 = _ekg_szavak(szoveg1)
    sz2, k2, v2 = _ekg_szavak(szoveg2)
    adat = {"szavak": (sz1, sz2), "kezdetek": (k1, k2), "vegek": (v1, v2),
            "blokkok": [], "mondat_id": [], "elso": {}, "utolso": {}}
    if not sz1 or not sz2:
        return adat
    # Mondatsorszám minden bal oldali szóhoz (mondatvég: .!?… vagy üres sor)
    veg_poz = [m.end() for m in re.finditer(r"[.!?…]+|\n\s*\n", szoveg1)]
    adat["mondat_id"] = [bisect_right(veg_poz, k) for k in k1]
    for wi, sid in enumerate(adat["mondat_id"]):
        adat["elso"].setdefault(sid, wi)
        adat["utolso"][sid] = wi + 1
    adat["blokkok"] = karakter_egyezo_blokkok(sz1, sz2)     # [(i, j, n)]
    return adat


# ============================================================================
# SZÍNBEÁLLÍTÁSOK (Szín menü) – a felhasználó fájlba mentve őrzi meg őket
# ============================================================================
SZIN_ALAP = {
    "paletta": ["#d9f2d9", "#dcecff", "#fff0b3", "#eadcf8", "#ffd9cc", "#d8f3f0", "#f1e0c5", "#e2e2f5"],
    "diff_paletta": ["#c8f7c5", "#bfe3ff", "#ffe1a8", "#e3cdf7", "#ffc9b3", "#c5f0ea", "#f2d9a0", "#d6d6f7"],
    "kijelolt_hatter": "#ffff00",
    "kijelolt_szoveg": "#000000",
    "hdiff_kijelolt": "#ffff00",
    "egyezes": "#c8f7c5",
    "ekg_vonal": "#43ff92",
    "ekg_szoveg": "#2f8a52",
}
SZINEK = {k: (list(v) if isinstance(v, list) else v) for k, v in SZIN_ALAP.items()}
SZIN_FAJL = str(Path.home() / ".sabtextcompar_colors.json")
_HEX_SZIN_RE = re.compile(r"^#[0-9a-fA-F]{6}$")


def szinek_betoltese():
    try:
        with open(SZIN_FAJL, "r", encoding="utf-8") as f:
            adat = json.load(f)
    except Exception:
        return
    if not isinstance(adat, dict):
        return
    for kulcs, alap in SZIN_ALAP.items():
        ertek = adat.get(kulcs)
        if isinstance(alap, list):
            if isinstance(ertek, list) and len(ertek) == len(alap) and all(
                    isinstance(x, str) and _HEX_SZIN_RE.match(x) for x in ertek):
                SZINEK[kulcs] = list(ertek)
        elif isinstance(ertek, str) and _HEX_SZIN_RE.match(ertek):
            SZINEK[kulcs] = ertek


def szinek_mentese():
    try:
        with open(SZIN_FAJL, "w", encoding="utf-8") as f:
            json.dump(SZINEK, f, indent=2)
    except OSError:
        pass


def _hex_rgb(h):
    return int(h[1:3], 16), int(h[3:5], 16), int(h[5:7], 16)


def szin_keveres(a, b, t):
    """Az `a` színből `t` (0..1) arányban a `b` felé keverve."""
    ra, rb = _hex_rgb(a), _hex_rgb(b)
    return "#%02x%02x%02x" % tuple(int(round(x + (y - x) * t)) for x, y in zip(ra, rb))


def szin_kontraszt(h):
    """Olvasható szövegszín (sötét vagy fehér) a megadott háttérhez."""
    r, g, b = _hex_rgb(h)
    return "#111111" if (0.299 * r + 0.587 * g + 0.114 * b) > 150 else "#ffffff"


szinek_betoltese()


# ============================================================================
# SZÖVEGFORMÁTUMOK - megnyitás és mentés
# ----------------------------------------------------------------------------
# Kizárólag a Python standard library-vel (zipfile, xml.etree, html.parser, zlib,
# struct), a nyilvános, nyílt szabványok alapján saját kóddal megvalósítva:
#   - kódolások: UTF-8 / UTF-8 BOM / UTF-16 / Windows-1250 / ISO-8859-2
#   - sima szöveges formátumok: txt, md, log, csv, tsv, json, xml, tex, rst,
#     srt, vtt, ass, ssa, sbv, lrc
#   - HTML (W3C/WHATWG), ODT (ISO/IEC 26300), DOCX (ISO/IEC 29500 / ECMA-376),
#     EPUB (W3C) - megnyitás
#   - HTML, ODT, DOCX - mentés a kijelölések színével és az aláhúzással
# Külső csomagot nem használ, így új licencnyilatkozat sem szükséges.
# ============================================================================
SZOVEG_KITERJESZTESEK = (".txt", ".srt", ".vtt", ".md", ".log", ".csv", ".tsv", ".json", ".xml",
                         ".tex", ".rst", ".ass", ".ssa", ".sbv", ".lrc", ".py")
DOKUMENTUM_KITERJESZTESEK = (".html", ".htm", ".docx", ".odt", ".epub")
TAMOGATOTT_KITERJESZTESEK = SZOVEG_KITERJESZTESEK + DOKUMENTUM_KITERJESZTESEK
FORMAZOTT_MENTES_KITERJESZTESEK = (".html", ".htm", ".docx", ".odt")
_MAX_ZIP_ELEM = 200 * 1024 * 1024          # egy tömörített elem kicsomagolt mérete legfeljebb ennyi lehet
_XML_TILTOTT_KAR = re.compile("[\x00-\x08\x0b\x0c\x0e-\x1f\ud800-\udfff\ufffe\uffff]")


def dekodol_szoveg(adat: bytes):
    """Bájtok -> (szöveg, kódolás). BOM, majd szigorú UTF-8, majd a régi magyar Windows-1250 /
    ISO-8859-2 kódolás; hibás bájt soha nem cserélődik némán „�”-re, ha van értelmes kódolás."""
    if adat.startswith(b"\xef\xbb\xbf"):
        return adat[3:].decode("utf-8", errors="replace"), "utf-8-sig"
    if adat.startswith((b"\xff\xfe", b"\xfe\xff")):
        try:
            return adat.decode("utf-16"), "utf-16"
        except UnicodeDecodeError:
            pass
    minta = adat[:4000]
    if len(minta) >= 4 and minta.count(b"\x00") > len(minta) * 0.25:      # BOM nélküli UTF-16
        kod = "utf-16-be" if minta[0::2].count(b"\x00") > minta[1::2].count(b"\x00") else "utf-16-le"
        try:
            return adat.decode(kod), kod
        except UnicodeDecodeError:
            pass
    for kod in ("utf-8", "cp1250", "iso8859_2"):
        try:
            return adat.decode(kod), kod
        except UnicodeDecodeError:
            continue
    return adat.decode("utf-8", errors="replace"), "utf-8"


def _sortoresek_egysegesitese(szoveg: str) -> str:
    return szoveg.replace("\r\n", "\n").replace("\r", "\n")


# ------------------------------------------------------------------- HTML
class _HtmlSzovegKinyero(HTMLParser):
    _BLOKK = {"p", "div", "br", "li", "tr", "h1", "h2", "h3", "h4", "h5", "h6", "section", "article",
              "header", "footer", "blockquote", "pre", "table", "ul", "ol", "hr", "dt", "dd", "figcaption"}
    _KIHAGY = {"script", "style", "template", "head"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.reszek = []
        self._kihagy = 0

    def handle_starttag(self, tag, attrs):
        if tag in self._KIHAGY:
            self._kihagy += 1
        elif tag in self._BLOKK and not self._kihagy:
            self.reszek.append("\n")

    def handle_startendtag(self, tag, attrs):
        if tag in self._BLOKK and not self._kihagy:
            self.reszek.append("\n")

    def handle_endtag(self, tag):
        if tag in self._KIHAGY:
            self._kihagy = max(0, self._kihagy - 1)
        elif tag in self._BLOKK and tag != "br" and not self._kihagy:
            self.reszek.append("\n")

    def handle_data(self, adat):
        if not self._kihagy:
            self.reszek.append(adat)


def html_szoveg_kinyerese(html_szoveg: str) -> str:
    p = _HtmlSzovegKinyero()
    p.feed(html_szoveg)
    p.close()
    szoveg = _sortoresek_egysegesitese("".join(p.reszek)).replace("\xa0", " ")
    szoveg = re.sub(r"[ \t\f\v]+", " ", szoveg)
    szoveg = re.sub(r" ?\n ?", "\n", szoveg)
    return re.sub(r"\n{3,}", "\n\n", szoveg).strip()


def _html_dekodolasa(adat: bytes) -> str:
    m = re.search(rb"<meta[^>]+charset\s*=\s*[\"']?\s*([A-Za-z0-9_\-]+)", adat[:4096], re.I)
    if m and not adat.startswith((b"\xef\xbb\xbf", b"\xff\xfe", b"\xfe\xff")):
        try:
            return adat.decode(m.group(1).decode("ascii"))
        except (UnicodeDecodeError, LookupError):
            pass
    return dekodol_szoveg(adat)[0]


# --------------------------------------------------- ZIP alapú dokumentumok
def _zip_elem(zf, nev: str) -> bytes:
    info = zf.getinfo(nev)
    if info.file_size > _MAX_ZIP_ELEM:
        raise ValueError(f"'{nev}' is too large.")
    return zf.read(nev)


def _biztonsagos_xml(bajtok: bytes):
    """XML beolvasása; a DTD / entitás-deklarációkat (XML-bomba) elutasítja."""
    if b"<!ENTITY" in bajtok or b"<!DOCTYPE" in bajtok:
        raise ValueError("Unsupported XML structure (DTD/entity declarations are not allowed).")
    return ET.fromstring(bajtok)


_W_NS = "{http://schemas.openxmlformats.org/wordprocessingml/2006/main}"


def docx_szoveg(utvonal) -> str:
    with zipfile.ZipFile(utvonal) as zf:
        gyoker = _biztonsagos_xml(_zip_elem(zf, "word/document.xml"))
    bekezdesek = []
    for p in gyoker.iter(_W_NS + "p"):
        reszek = []
        for e in p.iter():
            if e.tag == _W_NS + "t":
                reszek.append(e.text or "")
            elif e.tag == _W_NS + "tab":
                reszek.append("\t")
            elif e.tag in (_W_NS + "br", _W_NS + "cr"):
                reszek.append("\n")
            elif e.tag == _W_NS + "noBreakHyphen":
                reszek.append("-")
        bekezdesek.append("".join(reszek))
    return "\n".join(bekezdesek)


_ODT_TEXT = "{urn:oasis:names:tc:opendocument:xmlns:text:1.0}"
_ODT_OFFICE = "{urn:oasis:names:tc:opendocument:xmlns:office:1.0}"


def _odt_bekezdes_szoveg(elem) -> str:
    reszek = [elem.text or ""]
    for gyerek in elem:
        if gyerek.tag == _ODT_TEXT + "s":
            reszek.append(" " * int(gyerek.get(_ODT_TEXT + "c", "1") or 1))
        elif gyerek.tag == _ODT_TEXT + "tab":
            reszek.append("\t")
        elif gyerek.tag == _ODT_TEXT + "line-break":
            reszek.append("\n")
        elif gyerek.tag in (_ODT_TEXT + "note", _ODT_OFFICE + "annotation"):
            pass                                            # lábjegyzet / megjegyzés kihagyva
        else:
            reszek.append(_odt_bekezdes_szoveg(gyerek))
        reszek.append(gyerek.tail or "")
    return "".join(reszek)


def odt_szoveg(utvonal) -> str:
    with zipfile.ZipFile(utvonal) as zf:
        gyoker = _biztonsagos_xml(_zip_elem(zf, "content.xml"))
    bekezdesek = []

    def bejar(elem):
        for gyerek in elem:
            if gyerek.tag in (_ODT_TEXT + "p", _ODT_TEXT + "h"):
                bekezdesek.append(_odt_bekezdes_szoveg(gyerek))
            elif gyerek.tag != _ODT_OFFICE + "annotation":
                bejar(gyerek)
    torzs = gyoker.find(_ODT_OFFICE + "body")
    bejar(torzs if torzs is not None else gyoker)
    return "\n".join(bekezdesek)


def epub_szoveg(utvonal) -> str:
    with zipfile.ZipFile(utvonal) as zf:
        nevek = zf.namelist()
        sorrend = []
        try:
            cont = _biztonsagos_xml(_zip_elem(zf, "META-INF/container.xml"))
            opf_ut = next(e.get("full-path") for e in cont.iter() if e.tag.endswith("rootfile"))
            opf = _biztonsagos_xml(_zip_elem(zf, opf_ut))
            mappa = posixpath.dirname(opf_ut)
            manifest = {e.get("id"): e.get("href") for e in opf.iter() if e.tag.endswith("}item")}
            for e in opf.iter():
                if e.tag.endswith("}itemref") and manifest.get(e.get("idref")):
                    sorrend.append(posixpath.normpath(posixpath.join(mappa, unquote(manifest[e.get("idref")]))))
        except (KeyError, StopIteration, ValueError, ET.ParseError):
            sorrend = []
        sorrend = [n for n in sorrend if n in nevek] or sorted(
            n for n in nevek if n.lower().endswith((".xhtml", ".html", ".htm")))
        fejezetek = [html_szoveg_kinyerese(_html_dekodolasa(_zip_elem(zf, n))) for n in sorrend]
    return "\n\n".join(f for f in fejezetek if f)


def olvas_szoveg_fajl(utvonal) -> str:
    """Bármely támogatott formátum beolvasása sima szöveggé (a szöveges tartalom, formázás nélkül)."""
    ext = Path(utvonal).suffix.lower()
    if ext == ".docx":
        szoveg = docx_szoveg(utvonal)
    elif ext == ".odt":
        szoveg = odt_szoveg(utvonal)
    elif ext == ".epub":
        szoveg = epub_szoveg(utvonal)
    else:
        with open(utvonal, "rb") as f:
            adat = f.read()
        if ext in (".html", ".htm"):
            szoveg = html_szoveg_kinyerese(_html_dekodolasa(adat))
        else:
            szoveg = dekodol_szoveg(adat)[0]
    return _sortoresek_egysegesitese(szoveg)


# -------------------------------- kijelölések (színek, aláhúzás) kimentése
_MENTESBOL_KIHAGYOTT_TAGEK = {"sel", "mu_tores", "egyez_kijelolt", "hdiff_kijelolt", "ekg_hely"}


def _szin_hex6(widget, szin):
    if not szin:
        return None
    if re.fullmatch(r"#[0-9a-fA-F]{6}", szin):
        return szin[1:].lower()
    try:
        r, g, b = widget.winfo_rgb(szin)
        return "%02x%02x%02x" % (r >> 8, g >> 8, b >> 8)
    except tk.TclError:
        return None


def widget_futasok(widget, mod="teljes"):
    """A Text mező tartalma [(szöveg, stílus|None)] futásokban; stílus = (háttér, betűszín, aláhúzott).
    A címkék prioritása szerint, mint a képernyőn. A csak megjelenítési célú sortöréseket
    (mu_tores) és az átmeneti, aktuális-kijelölés címkéket kihagyja.

    A `mod` paraméterrel szűrhető, hogy mi kerüljön a kimenetbe:
      - "teljes"   - minden szöveg, úgy, ahogy a képernyőn látszik (alapértelmezett)
      - "egyezes"  - a képernyőn egyezésként megjelölt szakaszok
                    (Visual Match View / Hagyományos diff jelentős egyező szakaszai)
      - "elteres"  - az eltérésként megjelölt szakaszok.

    FONTOS: a Visual Match View saját, helyhez kötött egyezési blokkjaihoz
    külön segédfüggvény tartozik (`vizualis_widget_futasok`), mert azok nem
    egyszerűen a Text widget tagjeiből származnak.
    """
    sorrend = {t: i for i, t in enumerate(widget.tag_names())}
    gyorsitotar = {}

    def stilus_es_kategoria(aktiv):
        kulcs = frozenset(aktiv)
        if kulcs not in gyorsitotar:
            hatter = betu = None
            alahuzas = van_egyezes = van_elteres = False
            for t in sorted((t for t in aktiv if t not in _MENTESBOL_KIHAGYOTT_TAGEK), key=lambda x: sorrend.get(x, 0)):
                if t.startswith("egyez_") or t.startswith("hdiff_") or t == "egyezes":
                    van_egyezes = True
                if t in ("elter", "sor_elter"):
                    van_elteres = True
                b = _szin_hex6(widget, widget.tag_cget(t, "background"))
                f = _szin_hex6(widget, widget.tag_cget(t, "foreground"))
                u = str(widget.tag_cget(t, "underline")).lower()
                if b:
                    hatter = b
                if f:
                    betu = f
                if u in ("1", "true", "yes", "on"):
                    alahuzas = True
                elif u in ("0", "false", "no", "off"):
                    alahuzas = False
            stilus = (hatter, betu, alahuzas) if (hatter or betu or alahuzas) else None
            gyorsitotar[kulcs] = (stilus, van_egyezes, van_elteres)
        return gyorsitotar[kulcs]

    aktiv, nyers = set(), []
    for kulcs, ertek, _ in widget.dump("1.0", "end-1c", tag=True, text=True):
        if kulcs == "tagon":
            aktiv.add(ertek)
        elif kulcs == "tagoff":
            aktiv.discard(ertek)
        elif kulcs == "text" and "mu_tores" not in aktiv:
            stilus, van_egyezes, van_elteres = stilus_es_kategoria(aktiv)
            nyers.append((ertek, stilus, van_egyezes, van_elteres))

    if mod == "egyezes":
        nyers = [(t, s) if v_e else ("\n" * t.count("\n"), None) for t, s, v_e, v_d in nyers]
    elif mod == "elteres":
        nyers = [(t, s) if v_d else ("\n" * t.count("\n"), None) for t, s, v_e, v_d in nyers]
    else:
        nyers = [(t, s) for t, s, v_e, v_d in nyers]

    futasok = []
    for szoveg, stilus in nyers:
        if not szoveg:
            continue
        if futasok and futasok[-1][1] == stilus:
            futasok[-1] = (futasok[-1][0] + szoveg, stilus)
        else:
            futasok.append((szoveg, stilus))
    return futasok


def vizualis_widget_futasok(widget, blokkok, oldal, mod="egyezes"):
    """A Visual Match View tényleges blokkjai alapján készít menthető futásokat.

    `blokkok` pontosan a `_vizualis_egyezesi_blokkok()` eredménye.
    `oldal` 1 vagy 2, így ugyanazt a helyhez kötött egyezéslistát használjuk
    a bal és a jobb dokumentum mentésénél is.

    Ez a mentési út nem a Text widget aktuális színező tagjeitől függ:
    ezért akkor is helyesen ment, ha a Visual Match View 2–10 szavas
    küszöbe más, mint a hagyományos Diffé.
    """
    if mod not in ("egyezes", "elteres"):
        raise ValueError("vizualis_widget_futasok csak egyezes/elteres módhoz használható")

    text = widget.get("1.0", "end-1c")
    if not text:
        return []

    if oldal == 1:
        ranges = [(max(0, int(bl["start1"])), min(len(text), int(bl["end1"]))) for bl in blokkok]
    else:
        ranges = [(max(0, int(bl["start2"])), min(len(text), int(bl["end2"]))) for bl in blokkok]

    # Rendezés + átfedések összevonása. A Visual Match View normál esetben
    # eleve rendezett és nem átfedő blokkokat ad, de így a mentés robusztus marad.
    ranges = [(a, b) for a, b in sorted(ranges) if b > a]
    osszevont = []
    for a, b in ranges:
        if osszevont and a <= osszevont[-1][1]:
            osszevont[-1] = (osszevont[-1][0], max(osszevont[-1][1], b))
        else:
            osszevont.append((a, b))

    # A mu_tores csak megjelenítési sortörés. A teljes mentés ezt már kezeli;
    # a Visual Match mentésnél is eltávolítjuk, hogy ne kerüljenek mesterséges
    # sortörések a kimenetbe.
    mu_pozok = set()
    try:
        for kezdo in widget.tag_ranges("mu_tores")[0::2]:
            mu_pozok.add(int(widget.count("1.0", kezdo, "chars")[0]))
    except tk.TclError:
        pass
    if mu_pozok:
        karakterek = list(text)
        for pos in sorted(mu_pozok, reverse=True):
            if 0 <= pos < len(karakterek) and karakterek[pos] == "\n":
                del karakterek[pos]
        # A tagpozíciók a törlés előttiek, ezért a vizuális mentéshez
        # egyszerűbb a szöveget a widget aktuális tartalmából megtartani:
        # a mesterséges törések törlése csak akkor szükséges, ha valóban vannak.
        text = "".join(karakterek)
        # A blokkok pozíciói is a widget eredeti koordinátáihoz tartoznak.
        # mu_tores esetén a mentéshez ezeket újraszámoljuk az eredeti szövegből.
        # Mivel a mu_tores csak extra '\n', a legegyszerűbb megoldás az,
        # hogy a futásokat az eredeti koordinátákon képezzük, és a végén
        # eltávolítjuk a mu_tores karaktereit. Ezért itt visszaolvassuk az
        # eredeti widget-szöveget a pozíciókhoz.
        text = widget.get("1.0", "end-1c")

    # Stílus: egyezésnél használjuk az adott egyez_N tag színét, eltérésnél
    # nincs külön vizuális stílus. Ez a Word/ODT/HTML mentést is értelmesen
    # formázza, miközben a TXT tartalma természetesen ugyanaz marad.
    def egyezesi_stilus(start, end):
        if mod != "egyezes":
            return None
        index = _offset_to_tk_index(text, start)
        for bl in blokkok:
            a = bl["start1"] if oldal == 1 else bl["start2"]
            b = bl["end1"] if oldal == 1 else bl["end2"]
            if a <= start and end <= b:
                tag = f"egyez_{bl['id']}"
                try:
                    hatter = _szin_hex6(widget, widget.tag_cget(tag, "background"))
                    betu = _szin_hex6(widget, widget.tag_cget(tag, "foreground"))
                    return (hatter, betu, True) if (hatter or betu) else None
                except tk.TclError:
                    return None
        return None

    # A kimenetet folyamatos szakaszokra bontjuk, megtartva a sorvégeket.
    # Minden szakaszhoz pontosan meghatározzuk, hogy egyezés-e vagy eltérés.
    hatarok = {0, len(text)}
    for a, b in osszevont:
        hatarok.add(a)
        hatarok.add(b)
    hatarok = sorted(hatarok)

    def _hozzaad(resz, stilus):
        if not resz:
            return
        if futasok and futasok[-1][1] == stilus:
            futasok[-1] = (futasok[-1][0] + resz, stilus)
        else:
            futasok.append((resz, stilus))

    futasok = []
    # "egyezes" módban a kihagyott (nem-egyező) közbeeső részek miatt a
    # megmaradó egyezések összefolynának egyetlen szövegfolyammá - ezért, ha
    # egy korábbi egyezés után újabb egyezés következik, azt új sorba
    # tördeljük. "elteres" módban pedig, amikor egy egyezést hagyunk ki, azon
    # a helyen egy üres sort hagyunk, hogy látszódjon, hogy ott a szöveg
    # folytonos volt a másik dokumentumban. A beszúrást csak akkor végezzük
    # el ténylegesen, amikor tudjuk, hogy van még utána megtartott tartalom -
    # így sem az elejére, sem a végére nem kerül felesleges sortörés/üres sor.
    volt_mar_megtartott = False
    varakozo_ujsor = False
    varakozo_ures_sor = False

    for a, b in zip(hatarok, hatarok[1:]):
        if b <= a:
            continue
        koztes = text[a:b]
        if not koztes:
            continue
        egyezo = any(x <= a and b <= y for x, y in osszevont)
        kell = egyezo if mod == "egyezes" else not egyezo
        if not kell:
            if mod == "egyezes" and volt_mar_megtartott:
                varakozo_ujsor = True
            elif mod == "elteres" and egyezo and volt_mar_megtartott:
                varakozo_ures_sor = True
            continue

        if varakozo_ujsor:
            if not (futasok and futasok[-1][0].endswith("\n")):
                _hozzaad("\n", None)
            varakozo_ujsor = False
        if varakozo_ures_sor:
            if futasok and futasok[-1][0].endswith("\n"):
                _hozzaad("\n", None)
            else:
                _hozzaad("\n\n", None)
            varakozo_ures_sor = False

        # Csak a megjelenítési célú sortöréseket hagyjuk ki.
        # Ehhez a szakaszt eredeti pozíciókkal vizsgáljuk.
        if mu_pozok:
            darab = []
            elozo = a
            for pos in sorted(p for p in mu_pozok if a <= p < b):
                if pos > elozo:
                    darab.append((text[elozo:pos], egyezesi_stilus(elozo, pos)))
                elozo = pos + 1
            if elozo < b:
                darab.append((text[elozo:b], egyezesi_stilus(elozo, b)))
            reszletek = darab
        else:
            reszletek = [(koztes, egyezesi_stilus(a, b))]

        for resz, stilus in reszletek:
            _hozzaad(resz, stilus)
            if resz:
                volt_mar_megtartott = True

    return futasok


def _xml_szoveg(s: str) -> str:
    return _xml_escape(_XML_TILTOTT_KAR.sub("", s))


def _futasok_bekezdesekre(futasok):
    bekezdesek = [[]]
    for szoveg, stilus in futasok:
        for i, resz in enumerate(szoveg.split("\n")):
            if i > 0:
                bekezdesek.append([])
            if resz:
                bekezdesek[-1].append((resz, stilus))
    return bekezdesek


def futasok_html(futasok, cim="SzTextCompar") -> str:
    darabok = []
    for szoveg, stilus in futasok:
        e = _xml_szoveg(szoveg)
        if stilus:
            hatter, betu, alahuzas = stilus
            css = []
            if hatter:
                css.append(f"background-color:#{hatter}")
            if betu:
                css.append(f"color:#{betu}")
            if alahuzas:
                css.append("text-decoration:underline")
            darabok.append(f'<span style="{";".join(css)}">{e}</span>')
        else:
            darabok.append(e)
    return ('<!DOCTYPE html>\n<html><head><meta charset="utf-8">\n'
            f"<title>{_xml_szoveg(cim)}</title>\n"
            "<style>*{-webkit-print-color-adjust:exact;print-color-adjust:exact}"
            "body{margin:24px;background:#fff;color:#111}"
            ".sz{white-space:pre-wrap;overflow-wrap:anywhere;font-family:Consolas,'Courier New',monospace;"
            "font-size:14px;line-height:1.45}</style></head>\n"
            '<body><div class="sz">' + "".join(darabok) + "</div></body></html>\n")


_W_DOCUMENT_NS = ('xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main" '
                  'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"')


def futasok_docx_bajtok(futasok) -> bytes:
    def futas_xml(szoveg, stilus):
        rpr = ""
        if stilus:
            hatter, betu, alahuzas = stilus
            if betu:
                rpr += f'<w:color w:val="{betu}"/>'
            if alahuzas:
                rpr += '<w:u w:val="single"/>'
            if hatter:
                rpr += f'<w:shd w:val="clear" w:color="auto" w:fill="{hatter}"/>'
            rpr = f"<w:rPr>{rpr}</w:rPr>"
        reszek = []
        for i, darab in enumerate(szoveg.split("\t")):
            if i > 0:
                reszek.append("<w:tab/>")
            if darab:
                reszek.append(f'<w:t xml:space="preserve">{_xml_szoveg(darab)}</w:t>')
        return f"<w:r>{rpr}{''.join(reszek)}</w:r>"

    torzs = "".join("<w:p>" + "".join(futas_xml(t, s) for t, s in bek) + "</w:p>"
                    for bek in _futasok_bekezdesekre(futasok))
    dokumentum = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
                  f"<w:document {_W_DOCUMENT_NS}><w:body>{torzs}"
                  '<w:sectPr><w:pgSz w:w="11906" w:h="16838"/>'
                  '<w:pgMar w:top="1134" w:right="1134" w:bottom="1134" w:left="1134" '
                  'w:header="708" w:footer="708" w:gutter="0"/></w:sectPr></w:body></w:document>')
    stilusok = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
                '<w:styles xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main">'
                '<w:docDefaults><w:rPrDefault><w:rPr>'
                '<w:rFonts w:ascii="Courier New" w:hAnsi="Courier New" w:cs="Courier New" w:eastAsia="Courier New"/>'
                '<w:sz w:val="20"/><w:szCs w:val="20"/></w:rPr></w:rPrDefault>'
                '<w:pPrDefault><w:pPr><w:spacing w:after="0" w:line="240" w:lineRule="auto"/></w:pPr></w:pPrDefault>'
                '</w:docDefaults>'
                '<w:style w:type="paragraph" w:default="1" w:styleId="Normal"><w:name w:val="Normal"/></w:style>'
                '</w:styles>')
    tartalomtipusok = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
                       '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
                       '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
                       '<Default Extension="xml" ContentType="application/xml"/>'
                       '<Override PartName="/word/document.xml" ContentType="application/vnd.openxmlformats-'
                       'officedocument.wordprocessingml.document.main+xml"/>'
                       '<Override PartName="/word/styles.xml" ContentType="application/vnd.openxmlformats-'
                       'officedocument.wordprocessingml.styles+xml"/></Types>')
    gyoker_kapcsolat = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
                        '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
                        '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/'
                        'relationships/officeDocument" Target="word/document.xml"/></Relationships>')
    dok_kapcsolat = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
                     '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
                     '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/'
                     'relationships/styles" Target="styles.xml"/></Relationships>')
    puffer = io.BytesIO()
    with zipfile.ZipFile(puffer, "w", zipfile.ZIP_DEFLATED) as zf:
        zf.writestr("[Content_Types].xml", tartalomtipusok)
        zf.writestr("_rels/.rels", gyoker_kapcsolat)
        zf.writestr("word/document.xml", dokumentum)
        zf.writestr("word/_rels/document.xml.rels", dok_kapcsolat)
        zf.writestr("word/styles.xml", stilusok)
    return puffer.getvalue()


def _odt_szoveg_xml(szoveg: str, elozo_nem_szokoz: bool):
    """Egy szövegdarab ODF-jelölése (szóközök, tabulátorok). Visszaadja: (xml, az utolsó karakter nem szóköz)."""
    kimenet = []
    for tok in re.split(r"( +|\t)", szoveg):
        if not tok:
            continue
        if tok == "\t":
            kimenet.append("<text:tab/>")
            elozo_nem_szokoz = True
        elif tok[0] == " ":
            k = len(tok)
            if elozo_nem_szokoz and k == 1:
                kimenet.append(" ")
            elif elozo_nem_szokoz:
                kimenet.append(f' <text:s text:c="{k - 1}"/>')
            else:
                kimenet.append(f'<text:s text:c="{k}"/>')
            elozo_nem_szokoz = False
        else:
            kimenet.append(_xml_szoveg(tok))
            elozo_nem_szokoz = True
    return "".join(kimenet), elozo_nem_szokoz


def futasok_odt_bajtok(futasok) -> bytes:
    stilusnevek = {}
    torzs = []
    for bek in _futasok_bekezdesekre(futasok):
        elemek, elozo = [], False
        for szoveg, stilus in bek:
            xml, elozo = _odt_szoveg_xml(szoveg, elozo)
            if stilus:
                nev = stilusnevek.setdefault(stilus, f"T{len(stilusnevek) + 1}")
                xml = f'<text:span text:style-name="{nev}">{xml}</text:span>'
            elemek.append(xml)
        torzs.append(f'<text:p text:style-name="P1">{"".join(elemek)}</text:p>' if elemek
                     else '<text:p text:style-name="P1"/>')
    szoveg_stilusok = []
    for (hatter, betu, alahuzas), nev in stilusnevek.items():
        tul = []
        if hatter:
            tul.append(f'fo:background-color="#{hatter}"')
        if betu:
            tul.append(f'fo:color="#{betu}"')
        if alahuzas:
            tul.append('style:text-underline-style="solid" style:text-underline-width="auto" '
                       'style:text-underline-color="font-color"')
        szoveg_stilusok.append(f'<style:style style:name="{nev}" style:family="text">'
                               f'<style:text-properties {" ".join(tul)}/></style:style>')
    tartalom = ('<?xml version="1.0" encoding="UTF-8"?>'
                '<office:document-content '
                'xmlns:office="urn:oasis:names:tc:opendocument:xmlns:office:1.0" '
                'xmlns:style="urn:oasis:names:tc:opendocument:xmlns:style:1.0" '
                'xmlns:text="urn:oasis:names:tc:opendocument:xmlns:text:1.0" '
                'xmlns:fo="urn:oasis:names:tc:opendocument:xmlns:xsl-fo-compatible:1.0" office:version="1.2">'
                '<office:automatic-styles>'
                '<style:style style:name="P1" style:family="paragraph">'
                '<style:paragraph-properties fo:margin-top="0cm" fo:margin-bottom="0cm"/>'
                '<style:text-properties style:font-name="Courier New" fo:font-family="&apos;Courier New&apos;" '
                'style:font-family-generic="modern" fo:font-size="10pt"/></style:style>'
                + "".join(szoveg_stilusok) +
                '</office:automatic-styles><office:body><office:text>' + "".join(torzs) +
                '</office:text></office:body></office:document-content>')
    jegyzek = ('<?xml version="1.0" encoding="UTF-8"?>'
               '<manifest:manifest xmlns:manifest="urn:oasis:names:tc:opendocument:xmlns:manifest:1.0" '
               'manifest:version="1.2">'
               '<manifest:file-entry manifest:full-path="/" manifest:version="1.2" '
               'manifest:media-type="application/vnd.oasis.opendocument.text"/>'
               '<manifest:file-entry manifest:full-path="content.xml" manifest:media-type="text/xml"/>'
               '</manifest:manifest>')
    puffer = io.BytesIO()
    with zipfile.ZipFile(puffer, "w") as zf:
        zf.writestr(zipfile.ZipInfo("mimetype"), "application/vnd.oasis.opendocument.text",
                    compress_type=zipfile.ZIP_STORED)                 # az ODF szerint az első, tömörítetlen elem
        zf.writestr("META-INF/manifest.xml", jegyzek, compress_type=zipfile.ZIP_DEFLATED)
        zf.writestr("content.xml", tartalom, compress_type=zipfile.ZIP_DEFLATED)
    return puffer.getvalue()


def mentes_formazott(utvonal, futasok, cim="SzTextCompar"):
    """HTML / DOCX / ODT mentése a kijelölések színével és aláhúzásával (kiterjesztés szerint)."""
    ext = Path(utvonal).suffix.lower()
    if ext in (".html", ".htm"):
        with open(utvonal, "w", encoding="utf-8") as f:
            f.write(futasok_html(futasok, cim))
    elif ext == ".docx":
        with open(utvonal, "wb") as f:
            f.write(futasok_docx_bajtok(futasok))
    elif ext == ".odt":
        with open(utvonal, "wb") as f:
            f.write(futasok_odt_bajtok(futasok))
    else:
        raise ValueError(f"Unsupported format: {ext}")


# ------------------------------------------ a hullám kimentése képként
_ES_BETUK = {
    "0": "111101101101111", "1": "010110010010111", "2": "111001111100111", "3": "111001111001111",
    "4": "101101111001001", "5": "111100111001111", "6": "111100111101111", "7": "111001001010010",
    "8": "111101111101111", "9": "111101111001111", " ": "000000000000000",
}


def _hex_rgb_tuple(h):
    h = h.lstrip("#")
    return int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)


class _Raszter:
    """Nagyon egyszerű RGB raszter (PNG-íráshoz), külső csomag nélkül."""

    def __init__(self, w, h, hatter):
        self.w, self.h = w, h
        self.px = bytearray(bytes(_hex_rgb_tuple(hatter)) * (w * h))

    def vonal(self, x0, y0, x1, y1, szin, alfa=1.0):
        r, g, b = _hex_rgb_tuple(szin)
        x0, y0, x1, y1 = int(round(x0)), int(round(y0)), int(round(x1)), int(round(y1))
        for y in range(max(0, y0), min(self.h - 1, y1) + 1):
            for x in range(max(0, x0), min(self.w - 1, x1) + 1):
                i = (y * self.w + x) * 3
                self.px[i] = int(self.px[i] + (r - self.px[i]) * alfa)
                self.px[i + 1] = int(self.px[i + 1] + (g - self.px[i + 1]) * alfa)
                self.px[i + 2] = int(self.px[i + 2] + (b - self.px[i + 2]) * alfa)

    def szoveg(self, x, y, szoveg, szin, meret=2):
        r, g, b = _hex_rgb_tuple(szin)
        for ch in szoveg:
            minta = _ES_BETUK.get(ch)
            if minta is None:
                continue
            for sor in range(5):
                for oszl in range(3):
                    if minta[sor * 3 + oszl] == "1":
                        for dy in range(meret):
                            for dx in range(meret):
                                px_, py_ = x + oszl * meret + dx, y + sor * meret + dy
                                if 0 <= px_ < self.w and 0 <= py_ < self.h:
                                    i = (py_ * self.w + px_) * 3
                                    self.px[i:i + 3] = bytes((r, g, b))
            x += 4 * meret

    def toltott_vonal(self, pontok, szin, sugar, alfa):
        """Kerek végű, élsimított vastag törtvonal (lefedettség-alapú)."""
        w, h = self.w, self.h
        lefedettseg = bytearray(w * h)
        r2 = sugar + 0.5
        for (xa, ya), (xb, yb) in zip(pontok, pontok[1:]):
            hossz = math.hypot(xb - xa, yb - ya)
            n = max(1, int(hossz / 0.5))
            for k in range(n + 1):
                cx = xa + (xb - xa) * k / n
                cy = ya + (yb - ya) * k / n
                for y in range(max(0, int(cy - sugar - 1)), min(h, int(cy + sugar + 2))):
                    for x in range(max(0, int(cx - sugar - 1)), min(w, int(cx + sugar + 2))):
                        c = r2 - math.hypot(x + 0.5 - cx, y + 0.5 - cy)
                        if c > 0:
                            v = 255 if c >= 1 else int(c * 255)
                            i = y * w + x
                            if v > lefedettseg[i]:
                                lefedettseg[i] = v
        r, g, b = _hex_rgb_tuple(szin)
        px = self.px
        for i, v in enumerate(lefedettseg):
            if v:
                a = v / 255.0 * alfa
                j = i * 3
                px[j] = int(px[j] + (r - px[j]) * a)
                px[j + 1] = int(px[j + 1] + (g - px[j + 1]) * a)
                px[j + 2] = int(px[j + 2] + (b - px[j + 2]) * a)

    def png_bajtok(self) -> bytes:
        def chunk(tipus, adat):
            return (struct.pack(">I", len(adat)) + tipus + adat +
                    struct.pack(">I", zlib.crc32(tipus + adat) & 0xFFFFFFFF))
        sorok = b"".join(b"\x00" + bytes(self.px[y * self.w * 3:(y + 1) * self.w * 3]) for y in range(self.h))
        return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", self.w, self.h, 8, 2, 0, 0, 0)) +
                chunk(b"IDAT", zlib.compress(sorok, 6)) + chunk(b"IEND", b""))


class SotetGorgetosav(tk.Canvas):
    """Sötét témájú, jól megfogható görgetősáv (a natív ttk-sáv Windowson világos marad)."""
    HATTER, CSUSZKA, KIEMELT, MIN_HOSSZ = "#0f1317", "#3a4756", "#566579", 30

    def __init__(self, master, orient="vertical", command=None):
        vert = orient == "vertical"
        super().__init__(master, bg=self.HATTER, highlightthickness=0, bd=0,
                         width=16 if vert else 1, height=1 if vert else 16)
        self._vert, self._cmd = vert, command
        self._elso, self._utolso, self._fogott, self._felett = 0.0, 1.0, None, False
        self.bind("<Configure>", lambda e: self._rajz())
        self.bind("<ButtonPress-1>", self._le)
        self.bind("<B1-Motion>", self._huz)
        self.bind("<ButtonRelease-1>", lambda e: setattr(self, "_fogott", None))
        self.bind("<Enter>", lambda e: self._felett_allit(True))
        self.bind("<Leave>", lambda e: self._felett_allit(False))

    def set(self, elso, utolso):
        self._elso, self._utolso = float(elso), float(utolso)
        self._rajz()

    def _felett_allit(self, ertek):
        self._felett = ertek
        self._rajz()

    def _hossz(self):
        return max(1, self.winfo_height() if self._vert else self.winfo_width())

    def _csuszka(self):
        L = self._hossz()
        a, b = self._elso * L, self._utolso * L
        if b - a < self.MIN_HOSSZ:
            b = min(L, a + self.MIN_HOSSZ)
            a = max(0, b - self.MIN_HOSSZ)
        return a, b

    def _rajz(self):
        self.delete("all")
        a, b = self._csuszka()
        szin = self.KIEMELT if (self._felett or self._fogott is not None) else self.CSUSZKA
        if self._vert:
            w = self.winfo_width()
            self.create_rectangle(3, a + 1, w - 3, b - 1, fill=szin, outline="")
        else:
            h = self.winfo_height()
            self.create_rectangle(a + 1, 3, b - 1, h - 3, fill=szin, outline="")

    def _poz(self, e):
        return e.y if self._vert else e.x

    def _le(self, e):
        a, b = self._csuszka()
        p = self._poz(e)
        self._fogott = (p - a) if a <= p <= b else (b - a) / 2.0
        if not (a <= p <= b) and self._cmd:
            self._cmd("moveto", max(0.0, (p - self._fogott) / self._hossz()))
        self._rajz()

    def _huz(self, e):
        if self._fogott is not None and self._cmd:
            self._cmd("moveto", max(0.0, (self._poz(e) - self._fogott) / self._hossz()))


class EgyezesEKGNezet:
    """Teljes képernyős kétpaneles nézet + EKG-szerű egyezési hullámsáv."""

    TEMA = dict(
        hatter="#0f1317", panel="#151a20", szoveg_hatter="#12161b", szoveg="#e4e7ea",
        halvany="#8b97a3", ekg_hatter="#050f09", racs="#0d2a19", racs_erosebb="#175232",
        vonal="#43ff92", ragyogas="#0f6b3a", kurzor="#ffd23f", jobb_sav="#4dd0ff",
    )
    SZINTEK = ["#1c3527", "#20402d", "#255034", "#2a613c", "#2d7343", "#2f8a52"]
    MIN_LATHATO_SZO = 25    # ennyi szónál jobban nem lehet belenagyítani

    def __init__(self, fomenu, szoveg1, szoveg2, cimke1, cimke2, adat):
        self.fomenu = fomenu
        self.cimkek = (cimke1, cimke2)
        # a Szín menüben beállított színek
        self.TEMA = dict(EgyezesEKGNezet.TEMA)
        self.TEMA["vonal"] = SZINEK["ekg_vonal"]
        self.TEMA["ragyogas"] = szin_keveres("#000000", SZINEK["ekg_vonal"], 0.4)
        self.TEMA["kurzor"] = SZINEK["kijelolt_hatter"]
        self.SZINTEK = [szin_keveres("#12161b", SZINEK["ekg_szoveg"], t) for t in (0.28, 0.42, 0.56, 0.70, 0.85, 1.0)]
        self._akt = None
        self.szoveg = (szoveg1, szoveg2)
        self.szavak_szama = (len(adat["szavak"][0]), len(adat["szavak"][1]))
        self.N1, self.N2 = self.szavak_szama
        self.kezdetek = adat["kezdetek"]
        self.vegek = adat["vegek"]
        self.blokkok = adat["blokkok"]
        self._mondat_id, self._elso, self._utolso = adat["mondat_id"], adat["elso"], adat["utolso"]
        self.sorkezdetek = (self._sorkezdetek(szoveg1), self._sorkezdetek(szoveg2))
        self._horgonyok_epitese()
        self._szuro_futasok(2)

        self.v0, self.v1 = 0.0, float(self.N1)
        self._kurzor_w = None
        self._zar = False
        self._rajz_id = None
        self._jelolo_id = None
        self._figyelmen_kivul = [0.0, 0.0]
        self._pan = None
        self._utolso_x = None

        self._felulet_epitese(cimke1, cimke2)
        self._szovegek_cimkezese()
        self.win.after(60, self._rajz_kesleltet)
        self.win.after(120, self._jelolo_frissit)

    # ------------------------------------------------------------------ adatok
    @staticmethod
    def _sorkezdetek(szoveg):
        kezdetek, poz = [0], 0
        for sor in szoveg.split("\n")[:-1]:
            poz += len(sor) + 1
            kezdetek.append(poz)
        return kezdetek

    def _idx(self, oldal, offset):
        sk = self.sorkezdetek[oldal]
        sor = bisect_right(sk, offset)
        return f"{sor}.{offset - sk[sor - 1]}"

    def _index_offset(self, oldal, idx):
        sor, oszl = (int(x) for x in str(idx).split("."))
        sk = self.sorkezdetek[oldal]
        sor = max(1, min(sor, len(sk)))
        return sk[sor - 1] + oszl

    def _horgonyok_epitese(self):
        """Két szöveg közötti (bal szó <-> jobb szó) leképezés támpontjai."""
        pontok = [(0, 0)]
        for i, j, n in self.blokkok:
            if n >= EKG_KOTOPONT_MIN:
                pontok.append((i, j))
                pontok.append((i + n, j + n))
        pontok.append((self.N1, self.N2))
        self._hor_i = [p[0] for p in pontok]
        self._hor_j = [p[1] for p in pontok]

    @staticmethod
    def _interpol(xs, ys, x):
        k = bisect_right(xs, x) - 1
        if k < 0:
            return ys[0]
        if k >= len(xs) - 1:
            return ys[-1]
        dx = xs[k + 1] - xs[k]
        if dx <= 0:
            return ys[k]
        return ys[k] + (x - xs[k]) * (ys[k + 1] - ys[k]) / dx

    def _szint(self, szo, i0, i1):
        """Egy egyezési szakasz magassága 0..1 (a választott minimumhoz igazítva).

        `szo` a szakaszban ténylegesen egyező szavak száma, `i1 - i0` pedig a
        szakasz teljes (a köztük lévő, legfeljebb pár karakteres réseket is
        magába foglaló) szóhossza - lásd `_szuro_futasok`. A két érték nem
        feltétlenül egyezik: több, egymástól távol eső, csak véletlenül
        egyező rövid szótöredék (pl. gyakori kötőszavak) össze is
        vonódhat egyetlen szakasszá, ha a közéjük eső szöveg elég rövid.

        Teljes (1.0) magasságot ezért csak akkor adunk, ha a szakasz
        VALÓBAN, összefüggően egyezik (a `surusseg` = szo / hossz közel 1) -
        egy hosszú, csak elvétve egyező szavakkal tarkított, egyébként
        teljesen eltérő szövegrész nem kaphat maximális csúcsot, mert az
        elfedné, hogy a két szöveg ott ténylegesen nem egyezik (az EKG-n
        ilyenkor korábban tévesen egyetlen, folytonosan magas vonal
        látszott, elrejtve az utána következő, önálló egyezéseket is)."""
        m = self.minimum
        teljes = max(EKG_TELJES_SZO, m + 2)
        hossz = max(1, i1 - i0)
        surusseg = szo / hossz
        SURUSEG_KUSZOB = 0.75   # ez alatt a szakasz "ritkásnak" számít
        alap = 0.12 + 0.88 * min(1.0, (szo - m) / (teljes - m))
        if surusseg >= SURUSEG_KUSZOB:
            if szo >= teljes:
                return 1.0
        else:
            return max(0.05, alap * (surusseg / SURUSEG_KUSZOB))
        for sid in range(self._mondat_id[i0], self._mondat_id[i1 - 1] + 1):
            if sid in self._elso:
                a, b = self._elso[sid], self._utolso[sid]
                if a >= i0 and b <= i1 and (b - a) >= EKG_MIN_MONDAT:
                    return 1.0      # egy teljes mondat egyezik
        return alap

    def _szuro_futasok(self, minimum):
        """Ugyanaz a szűrés és összevonás, mint az „Egyezések vizuális nézete”-ben
        (legalább `minimum` szavas pontos egyezések; ≤8 karakternyi rés esetén összevonva)."""
        self.minimum = minimum
        sz0, sz1 = self.szoveg
        ossz = []       # [i0, i1, j0, j1, szavak]
        for i, j, n in self.blokkok:
            if n < minimum:
                continue
            if ossz:
                e = ossz[-1]
                g1 = sz0[self.vegek[0][e[1] - 1]:self.kezdetek[0][i]].strip()
                g2 = sz1[self.vegek[1][e[3] - 1]:self.kezdetek[1][j]].strip()
                if len(g1) <= 8 and len(g2) <= 8:
                    e[1], e[3], e[4] = i + n, j + n, e[4] + n
                    continue
            ossz.append([i, i + n, j, j + n, n])
        self.mutatott = ossz
        self.R_i0 = [e[0] for e in ossz]
        self.R_i1 = [e[1] for e in ossz]
        self.R_j0 = [e[2] for e in ossz]
        self.R_j1 = [e[3] for e in ossz]
        self.R_lv = [self._szint(e[4], e[0], e[1]) for e in ossz]

    def _futas_keres(self, a, b):
        """A [a, b] bal-szótartományt metsző legmagasabb egyezés indexe (vagy None)."""
        k = bisect_right(self.R_i1, a)
        legjobb, szint = None, -1.0
        while k < len(self.R_i0) and self.R_i0[k] <= b:
            if self.R_lv[k] > szint:
                szint, legjobb = self.R_lv[k], k
            k += 1
        return legjobb

    # ---------------------------------------------------------------- felület
    def _gomb(self, szulo, szoveg, parancs):
        return tk.Button(szulo, text=tr(szoveg), command=parancs, bg="#232b33", fg="#e4e7ea",
                         activebackground="#33404b", activeforeground="#ffffff", relief="flat",
                         bd=0, padx=10, pady=3, cursor="hand2", font=("Segoe UI", 9))

    def _felulet_epitese(self, cimke1, cimke2):
        T = self.TEMA
        win = self.win = tk.Toplevel(self.fomenu)
        win.title(tr("Egyezési hullám – teljes képernyő"))
        win.configure(bg=T["hatter"])
        try:
            win.attributes("-fullscreen", True)
        except tk.TclError:
            try:
                win.state("zoomed")
            except tk.TclError:
                win.geometry("1400x850+20+20")
        win.protocol("WM_DELETE_WINDOW", self._bezar)

        # --- felső eszköztár
        bar = tk.Frame(win, bg=T["panel"])
        bar.pack(side="top", fill="x")
        tk.Label(bar, text=tr("Egyezési hullám – teljes képernyő"), bg=T["panel"], fg=T["szoveg"],
                 font=("Segoe UI", 11, "bold")).pack(side="left", padx=10, pady=6)
        tk.Label(bar, text=tr("Min. egyező szó:"), bg=T["panel"], fg=T["halvany"],
                 font=("Segoe UI", 9)).pack(side="left", padx=(18, 4))
        self.min_var = tk.IntVar(value=2)
        om = tk.OptionMenu(bar, self.min_var, *range(2, 11), command=lambda v: self._min_valtozott())
        om.configure(bg="#232b33", fg=T["szoveg"], activebackground="#33404b", activeforeground="#ffffff",
                     highlightthickness=0, relief="flat", bd=0, width=4, padx=10, pady=4,
                     font=("Segoe UI", 12, "bold"), cursor="hand2")
        om["menu"].configure(bg="#232b33", fg=T["szoveg"], activebackground="#3a5f8a",
                             activeforeground="#ffffff", font=("Segoe UI", 12), bd=0)
        om.pack(side="left")
        self.sync_var = tk.BooleanVar(value=True)
        tk.Checkbutton(bar, text=tr("Szinkron görgetés"), variable=self.sync_var, bg=T["panel"],
                       fg=T["szoveg"], selectcolor=T["hatter"], activebackground=T["panel"],
                       activeforeground="#ffffff", highlightthickness=0,
                       font=("Segoe UI", 9)).pack(side="left", padx=(18, 8))
        for jel, irany in (("◀", -1), ("▶", 1)):       # előző / következő egyezés
            tk.Button(bar, text=jel, command=lambda d=irany: self._lep(d), bg="#232b33", fg="#e4e7ea",
                      activebackground="#33404b", activeforeground="#ffffff", relief="flat", bd=0,
                      padx=14, pady=2, cursor="hand2", font=("Segoe UI", 13, "bold")).pack(side="left", padx=2)
        self._gomb(bar, "✕ Kilépés (Esc)", self._bezar).pack(side="right", padx=8, pady=5)
        self._gomb(bar, "F11 teljes/ablak", self._teljes_kapcsolo).pack(side="right", padx=2, pady=5)

        # --- fő terület: felül a két szöveg, alul az EKG
        self.paned = tk.PanedWindow(win, orient="vertical", sashwidth=7, bd=0, bg=T["hatter"],
                                    sashrelief="flat")
        self.paned.pack(side="top", fill="both", expand=True)

        felso = tk.Frame(self.paned, bg=T["hatter"])
        felso.columnconfigure(0, weight=1, uniform="p")
        felso.columnconfigure(1, weight=1, uniform="p")
        felso.rowconfigure(1, weight=1)
        self.texts = []
        for oldal, cimke in enumerate((cimke1, cimke2)):
            tk.Label(felso, text=cimke, bg=T["hatter"], fg=T["halvany"], anchor="w",
                     font=("Segoe UI", 9, "bold")).grid(row=0, column=oldal, sticky="ew", padx=8, pady=(4, 0))
            keret = tk.Frame(felso, bg=T["hatter"])
            keret.grid(row=1, column=oldal, sticky="nsew", padx=(6, 6), pady=4)
            keret.rowconfigure(0, weight=1)
            keret.columnconfigure(0, weight=1)
            w = tk.Text(keret, wrap="word", font=("Consolas", 13), bg=T["szoveg_hatter"],
                        fg=T["szoveg"], insertbackground=T["szoveg"], relief="flat", bd=0,
                        padx=10, pady=8, spacing1=2, spacing3=2, selectbackground="#3a5f8a",
                        selectforeground="#ffffff", highlightthickness=1,
                        highlightbackground="#232b33", highlightcolor="#3a5f8a")
            w.grid(row=0, column=0, sticky="nsew")
            vsb = SotetGorgetosav(keret, "vertical", w.yview)
            vsb.grid(row=0, column=1, sticky="ns", padx=(3, 0))
            w.configure(yscrollcommand=self._yscroll_kezelo(oldal, vsb))
            w.insert("1.0", self.szoveg[oldal])
            for n, szin in enumerate(self.SZINTEK):
                w.tag_configure(f"ekg_l{n}", background=szin, foreground=szin_kontraszt(szin))
            w.tag_configure("ekg_hely", background=T["kurzor"], foreground=SZINEK["kijelolt_szoveg"], underline=True)
            w.tag_raise("ekg_hely")
            w.tag_raise("sel")
            w.bind("<Button-1>", lambda e, ww=w: ww.focus_set(), add="+")
            w.configure(state="disabled")
            self.texts.append(w)
        self.paned.add(felso, stretch="always", minsize=160)

        also = tk.Frame(self.paned, bg=T["ekg_hatter"])
        fej = tk.Frame(also, bg=T["panel"])
        fej.pack(side="top", fill="x")
        self.info_var = tk.StringVar(
            value=tr("Kattintás / húzás: ugrás mindkét szövegben  •  Görgő: nagyítás  •  "
                     "Shift+görgő / jobb gomb húzása: eltolás"))
        tk.Label(fej, textvariable=self.info_var, bg=T["panel"], fg=T["vonal"], anchor="w",
                 font=("Segoe UI", 9)).pack(side="left", padx=8, pady=3, fill="x", expand=True)
        self._gomb(fej, "💾 Kép mentése", self._kep_mentese).pack(side="right", padx=(2, 10), pady=2)
        self._gomb(fej, "⟲ Teljes", self._nezet_visszaallitas).pack(side="right", padx=(2, 6), pady=2)
        self._gomb(fej, "+", lambda: self._nagyit(1.6)).pack(side="right", padx=2, pady=2)
        self._gomb(fej, "−", lambda: self._nagyit(1 / 1.6)).pack(side="right", padx=2, pady=2)

        self.canvas = tk.Canvas(also, height=230, bg=T["ekg_hatter"], highlightthickness=0, bd=0,
                                cursor="crosshair")
        self.canvas.pack(side="top", fill="both", expand=True)
        self.hsb = SotetGorgetosav(also, "horizontal", self._vszkroll)
        self.hsb.pack(side="bottom", fill="x")
        self.paned.add(also, stretch="never", minsize=120)

        c = self.canvas
        c.bind("<Configure>", lambda e: self._rajz_kesleltet())
        c.bind("<ButtonPress-1>", self._bal_le)
        c.bind("<B1-Motion>", self._bal_huz)
        c.bind("<Motion>", self._eger_mozog)
        c.bind("<Leave>", lambda e: self.info_var.set(""))
        for gomb in (2, 3):
            c.bind(f"<ButtonPress-{gomb}>", self._pan_le)
            c.bind(f"<B{gomb}-Motion>", self._pan_huz)
        c.bind("<MouseWheel>", self._kerek)
        c.bind("<Button-4>", self._kerek)
        c.bind("<Button-5>", self._kerek)

        win.bind("<Escape>", lambda e: self._bezar())
        win.bind("<F11>", self._teljes_kapcsolo)
        win.bind("<Left>", lambda e: self._eltol_aranyban(-0.1))
        win.bind("<Right>", lambda e: self._eltol_aranyban(0.1))
        win.bind("<Home>", lambda e: self._nezet_visszaallitas())
        for k in ("<plus>", "<KP_Add>", "<equal>"):
            win.bind(k, lambda e: self._nagyit(1.4))
        for k in ("<minus>", "<KP_Subtract>"):
            win.bind(k, lambda e: self._nagyit(1 / 1.4))
        win.focus_force()

    def _teljes_kapcsolo(self, event=None):
        try:
            uj = not bool(int(self.win.attributes("-fullscreen")))
            self.win.attributes("-fullscreen", uj)
            if not uj:
                self.win.geometry("1400x850+40+40")
        except tk.TclError:
            pass

    def _bezar(self):
        self._zar = True
        for azon in (self._rajz_id, self._jelolo_id):
            if azon is not None:
                try:
                    self.win.after_cancel(azon)
                except (ValueError, tk.TclError):
                    pass
        try:
            self.win.destroy()
        except tk.TclError:
            pass

    # ------------------------------------------------------- szövegpanelek
    def _szovegek_cimkezese(self):
        """Az egyező szavak háttérszínezése (erősebb egyezés = erősebb zöld)."""
        for oldal in (0, 1):
            w = self.texts[oldal]
            for n in range(len(self.SZINTEK)):
                w.tag_remove(f"ekg_l{n}", "1.0", "end")
            csoportok = [[] for _ in self.SZINTEK]
            for k, e in enumerate(self.mutatott):
                a, b = (e[0], e[1]) if oldal == 0 else (e[2], e[3])
                q = min(len(self.SZINTEK) - 1, int(self.R_lv[k] * len(self.SZINTEK)))
                csoportok[q].append(self._idx(oldal, self.kezdetek[oldal][a]))
                csoportok[q].append(self._idx(oldal, self.vegek[oldal][b - 1]))
            for q, lista in enumerate(csoportok):
                for r in range(0, len(lista), 2000):
                    w.tag_add(f"ekg_l{q}", *lista[r:r + 2000])

    def _futasra(self, k):
        """Ugrás a k-adik egyezésre mindkét panelben (és a hullám arra a részre görget)."""
        i0, i1, j0, j1 = self.R_i0[k], self.R_i1[k], self.R_j0[k], self.R_j1[k]
        if i1 - i0 <= 40:
            jel_bal, jel_jobb = (i0, i1), (j0, j1)
        else:
            jel_bal, jel_jobb = (i0, i0 + 11), (j0, min(j1, j0 + 11))
        self._ugras(i0, j0, jel_bal, jel_jobb, i0 + 0.5)
        self._akt = k
        if not (self.v0 <= i0 < self.v1):
            span = self.v1 - self.v0
            self._nezet_beallit(i0 - span / 2, i0 + span / 2)
        self.info_var.set(f"{k + 1} / {len(self.R_i0)}")

    def _lep(self, irany):
        """Előző (-1) / következő (+1) egyezésre lépés."""
        n = len(self.R_i0)
        if not n:
            return
        if self._akt is not None and 0 <= self._akt < n:
            k = self._akt + irany
        else:
            elso_lepes = self._kurzor_w is None      # még nem volt kattintás/ugrás
            try:
                pos = self._kurzor_w if self._kurzor_w is not None else self._lathato_tartomany(0)[0]
            except tk.TclError:
                pos = 0
            if irany > 0:
                k = bisect_left(self.R_i0, pos) if elso_lepes else bisect_right(self.R_i0, pos)
            else:
                k = bisect_left(self.R_i0, pos) - 1
        k = max(0, min(n - 1, k))
        self._futasra(k)

    def _min_valtozott(self, event=None):
        self._akt = None
        try:
            m = max(2, min(10, int(self.min_var.get())))
        except (ValueError, tk.TclError):
            m = 2
        self.min_var.set(m)
        self._szuro_futasok(m)
        self._szovegek_cimkezese()
        self._rajz_kesleltet()

    def _gorgetes_szohoz(self, oldal, szo, felette=4):
        n = self.szavak_szama[oldal]
        szo = max(0, min(int(szo), n - 1))
        idx = self._idx(oldal, self.kezdetek[oldal][szo])
        w = self.texts[oldal]
        self._figyelmen_kivul[oldal] = time.monotonic() + 0.25
        try:
            w.yview(f"{idx} - {felette} display lines" if felette else idx)
        except tk.TclError:
            w.see(idx)

    def _yscroll_kezelo(self, oldal, vsb):
        def kezelo(elso, utolso):
            vsb.set(elso, utolso)
            if not self._zar:
                self._pane_gorgetve(oldal)
        return kezelo

    def _pane_gorgetve(self, oldal):
        self._jelolo_frissit()
        if not self.sync_var.get() or time.monotonic() < self._figyelmen_kivul[oldal]:
            return
        try:
            top = self._index_offset(oldal, self.texts[oldal].index("@0,0"))
        except tk.TclError:
            return
        sz = min(bisect_right(self.vegek[oldal], top), self.szavak_szama[oldal] - 1)
        if oldal == 0:
            cel = self._interpol(self._hor_i, self._hor_j, sz)
        else:
            cel = self._interpol(self._hor_j, self._hor_i, sz)
        self._gorgetes_szohoz(1 - oldal, cel, felette=0)

    def _lathato_tartomany(self, oldal):
        """A panelben látható szavak [a, b) tartománya."""
        w = self.texts[oldal]
        top = self._index_offset(oldal, w.index("@0,0"))
        bot = self._index_offset(oldal, w.index(f"@0,{max(0, w.winfo_height() - 1)}"))
        n = self.szavak_szama[oldal]
        a = min(bisect_right(self.vegek[oldal], top), n - 1)
        b = max(a + 1, min(n, bisect_right(self.kezdetek[oldal], bot)))
        return a, b

    def _ugras(self, bal_szo, jobb_szo, jel_bal, jel_jobb, kurzor_w):
        """Mindkét panel egyszerre odaugrik + a kiválasztott szavak sárga jelölése."""
        self._gorgetes_szohoz(0, bal_szo)
        self._gorgetes_szohoz(1, jobb_szo)
        for oldal, (a, b) in ((0, jel_bal), (1, jel_jobb)):
            w = self.texts[oldal]
            w.tag_remove("ekg_hely", "1.0", "end")
            b = min(b, self.szavak_szama[oldal])
            if a < b:
                w.tag_add("ekg_hely", self._idx(oldal, self.kezdetek[oldal][a]),
                          self._idx(oldal, self.vegek[oldal][b - 1]))
        self._kurzor_w = kurzor_w
        self._jelolo_frissit()

    # ------------------------------------------------------- nézet (zoom/pan)
    def _nezet_beallit(self, v0, v1):
        span = max(min(self.N1, self.MIN_LATHATO_SZO), min(v1 - v0, float(self.N1)))
        v0 = max(0.0, min(v0, self.N1 - span))
        self.v0, self.v1 = v0, v0 + span
        self.hsb.set(self.v0 / self.N1, self.v1 / self.N1)
        self._rajz_kesleltet()

    def _nezet_visszaallitas(self):
        self._nezet_beallit(0.0, float(self.N1))

    def _nagyit(self, tenyezo, x=None):
        W = max(1, self.canvas.winfo_width())
        x = W / 2 if x is None else x
        span = self.v1 - self.v0
        horgony = self.v0 + span * x / W
        uj = span / tenyezo
        self._nezet_beallit(horgony - uj * (x / W), horgony + uj * (1 - x / W))

    def _eltol_aranyban(self, arany):
        span = self.v1 - self.v0
        self._nezet_beallit(self.v0 + span * arany, self.v1 + span * arany)

    def _vszkroll(self, *args):
        span = self.v1 - self.v0
        if args[0] == "moveto":
            uj = float(args[1]) * self.N1
        else:
            n = int(args[1])
            uj = self.v0 + n * span * (0.9 if args[2] == "pages" else 0.1)
        self._nezet_beallit(uj, uj + span)

    def _kerek(self, event):
        num = getattr(event, "num", None)
        if num == 4:
            irany = 1
        elif num == 5:
            irany = -1
        else:
            irany = 1 if event.delta > 0 else -1
        if event.state & 0x1:                       # Shift + görgő = eltolás
            self._eltol_aranyban(-irany * 0.15)
        else:
            self._nagyit(1.25 if irany > 0 else 1 / 1.25, event.x)

    def _pan_le(self, event):
        self._pan = (event.x, self.v0, self.v1 - self.v0)

    def _pan_huz(self, event):
        if not self._pan:
            return
        x0, v0, span = self._pan
        ppw = max(1, self.canvas.winfo_width()) / span
        self._nezet_beallit(v0 - (event.x - x0) / ppw, v0 - (event.x - x0) / ppw + span)

    # -------------------------------------------------- kattintás, ugrás, hover
    def _szo_x_bol(self, x):
        W = max(1, self.canvas.winfo_width())
        ppw = W / (self.v1 - self.v0)
        return self.v0 + x / ppw, ppw

    def _bal_le(self, event):
        self._utolso_x = None
        self._kattintas(event.x)

    def _bal_huz(self, event):
        if event.x != self._utolso_x:
            self._kattintas(event.x)

    def _kattintas(self, x):
        self._utolso_x = x
        w, ppw = self._szo_x_bol(x)
        w = max(0.0, min(w, self.N1 - 1e-6))
        tol = 4.0 / ppw
        k = self._futas_keres(w - tol, w + tol)
        if k is not None:
            i0, i1, j0, j1 = self.R_i0[k], self.R_i1[k], self.R_j0[k], self.R_j1[k]
            n = i1 - i0
            wi = int(min(max(w, i0), i1 - 1))

            def jobb(x):
                return min(j1, j0 + int(round((x - i0) * (j1 - j0) / max(1, n))))
            if n <= 40:
                a, b = i0, i1
                ja, jb = j0, j1
            else:
                a, b = max(i0, wi - 5), min(i1, wi + 6)
                ja, jb = jobb(a), max(jobb(a) + 1, jobb(b))
            self._ugras(wi, min(j1 - 1, jobb(wi)), (a, b), (ja, jb), w)
            self._akt = k
        else:
            li = int(w)
            rj = max(0, min(self.N2 - 1, int(self._interpol(self._hor_i, self._hor_j, w))))
            self._ugras(li, rj, (li, li + 1), (rj, rj + 1), w)
            self._akt = None

    def _eger_mozog(self, event):
        w, ppw = self._szo_x_bol(event.x)
        k = self._futas_keres(w - 3.0 / ppw, w + 3.0 / ppw)
        if k is None:
            self.info_var.set(tr("Nincs egyezés itt"))
            return
        i0, n = self.R_i0[k], self.R_i1[k] - self.R_i0[k]
        s = " ".join(self.szoveg[0][self.kezdetek[0][i0]:self.vegek[0][i0 + n - 1]].split())
        if len(s) > 90:
            s = s[:90] + "…"
        self.info_var.set(f"{n} {tr('egyező szó')}: „{s}”")

    # ------------------------------------------------------------- rajzolás
    @staticmethod
    def _szep_lepes(min_lepes):
        if min_lepes <= 1:
            return 1
        exp = 10 ** int(math.floor(math.log10(min_lepes)))
        for m in (1, 2, 5, 10):
            if m * exp >= min_lepes:
                return m * exp

    def _rajz_kesleltet(self):
        if self._zar or self._rajz_id is not None:
            return
        self._rajz_id = self.win.after(16, self._rajzol)

    def _jelolo_frissit(self):
        if self._zar or self._jelolo_id is not None:
            return
        self._jelolo_id = self.win.after(30, self._jelolo_rajzol)

    def _kep_geometria(self, W, H):
        felso, ruler = 42, 30
        alap = H - ruler - 8
        return felso, ruler, alap, max(10, alap - felso)

    def _kep_tickek(self, W):
        ppw = W / self.N1
        lepes = self._szep_lepes(110.0 / ppw)
        t, ertekek = lepes, []
        while t <= self.N1:
            ertekek.append((t * ppw, f"{int(t):,}".replace(",", " ")))
            t += lepes
        return ertekek

    def _kep_svg(self, W, H):
        """A teljes egyezési hullám vektoros (SVG) képe a szöveg teljes hosszában."""
        T = self.TEMA
        felso, ruler, alap, magassag = self._kep_geometria(W, H)
        pontok = self._hullam_pontok(W, alap, magassag, 0.0, float(self.N1))
        pt = " ".join(f"{x:.1f},{y:.1f}" for x, y in pontok)
        r = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">',
             f'<rect width="{W}" height="{H}" fill="{T["ekg_hatter"]}"/>']
        for f in (0.25, 0.5, 0.75, 1.0):
            y = alap - f * magassag
            r.append(f'<line x1="0" y1="{y:.1f}" x2="{W}" y2="{y:.1f}" stroke="{T["racs"]}" stroke-dasharray="3 5"/>')
        for x, cim in self._kep_tickek(W):
            r.append(f'<line x1="{x:.1f}" y1="{felso - 6}" x2="{x:.1f}" y2="{H - ruler}" stroke="{T["racs"]}"/>')
            r.append(f'<text x="{x + 4:.1f}" y="{H - ruler + 16}" font-family="Segoe UI, Arial, sans-serif" '
                     f'font-size="12" fill="{T["halvany"]}">{cim}</text>')
        r.append(f'<line x1="0" y1="{H - ruler}" x2="{W}" y2="{H - ruler}" stroke="{T["racs_erosebb"]}"/>')
        r.append(f'<line x1="0" y1="{alap}" x2="{W}" y2="{alap}" stroke="{T["racs_erosebb"]}"/>')
        felirat = f"{self.cimkek[0]}  ↔  {self.cimkek[1]}    ·    " + tr(f"{self.N1} szó")
        r.append(f'<text x="10" y="22" font-family="Segoe UI, Arial, sans-serif" font-size="14" '
                 f'fill="{T["vonal"]}">{_xml_szoveg(felirat)}</text>')
        r.append(f'<polyline points="{pt}" fill="none" stroke="{T["ragyogas"]}" stroke-width="6" '
                 'stroke-linejoin="round" stroke-linecap="round" stroke-opacity="0.75"/>')
        r.append(f'<polyline points="{pt}" fill="none" stroke="{T["vonal"]}" stroke-width="2" '
                 'stroke-linejoin="round" stroke-linecap="round"/>')
        r.append("</svg>")
        return "\n".join(r)

    def _kep_png(self, W, H):
        """Ugyanez PNG-ben (saját, külső csomag nélküli rasztermotorral)."""
        T = self.TEMA
        felso, ruler, alap, magassag = self._kep_geometria(W, H)
        pontok = self._hullam_pontok(W, alap, magassag, 0.0, float(self.N1))
        rz = _Raszter(W, H, T["ekg_hatter"])
        for f in (0.25, 0.5, 0.75, 1.0):
            y = alap - f * magassag
            rz.vonal(0, y, W - 1, y, T["racs"], 0.8)
        for x, cim in self._kep_tickek(W):
            rz.vonal(x, felso - 6, x, H - ruler, T["racs"])
            rz.vonal(x, H - ruler, x, H - ruler + 5, T["halvany"])
            rz.szoveg(int(x) + 4, H - ruler + 9, cim, T["halvany"])
        rz.vonal(0, H - ruler, W - 1, H - ruler, T["racs_erosebb"])
        rz.vonal(0, alap, W - 1, alap, T["racs_erosebb"])
        rz.toltott_vonal(pontok, T["ragyogas"], 4.0, 0.75)
        rz.toltott_vonal(pontok, T["vonal"], 1.3, 1.0)
        return rz.png_bajtok()

    def _kep_mentese(self):
        """A hullám teljes hosszának mentése SVG (vektoros) vagy PNG képként."""
        utvonal = filedialog.asksaveasfilename(
            parent=self.win, title=tr("Hullám mentése képként"), initialfile="hullam.svg",
            defaultextension=".svg",
            filetypes=[("SVG kép (vektoros)", "*.svg"), ("PNG kép", "*.png")])
        if not utvonal:
            return
        ext = Path(utvonal).suffix.lower()
        if ext not in (".svg", ".png"):
            utvonal, ext = utvonal + ".svg", ".svg"
        try:
            if ext == ".png":
                with open(utvonal, "wb") as f:
                    f.write(self._kep_png(2000, 360))
            else:
                with open(utvonal, "w", encoding="utf-8") as f:
                    f.write(self._kep_svg(2000, 360))
            messagebox.showinfo(tr("Mentve"), tr(f"Sikeresen elmentve:\n{utvonal}"), parent=self.win)
        except Exception as e:
            messagebox.showerror(tr("Hiba"), tr(f"Nem sikerült menteni:\n{e}"), parent=self.win)

    def _hullam_pontok(self, W, alap, magassag, v0, v1):
        """Az egyezési hullám törtvonalának pontjai a [v0, v1) szótartományra, W pixel szélességben
        (a képernyőn és a képként mentésnél is ugyanez)."""
        ppw = W / (v1 - v0)

        def Y(szint):
            return alap - szint * magassag

        k0 = bisect_right(self.R_i1, v0)
        k1 = bisect_left(self.R_i0, v1)
        pontok = []
        if ppw >= 2.5:
            # nagyítva: futásonként EKG-szerű, dőlt szárú csúcsok
            e = min(4.0, max(1.0, ppw * 0.35))
            elozo = None
            pontok.append((-20.0, alap))
            for k in range(k0, k1):
                x0 = (self.R_i0[k] - v0) * ppw
                x1 = (self.R_i1[k] - v0) * ppw
                yt = Y(self.R_lv[k])
                if elozo is None:
                    pontok.append((x0 - e, alap))
                elif x0 - elozo >= 2 * e:
                    pontok.append((elozo + e, alap))
                    pontok.append((x0 - e, alap))
                else:
                    pontok.append(((elozo + x0) / 2, alap))
                pontok.append((x0, yt))
                pontok.append((x1, yt))
                elozo = x1
            if elozo is not None:
                pontok.append((elozo + e, alap))
            pontok.append((W + 20.0, alap))
        else:
            # kicsinyítve: pixeloszloponként a legmagasabb csúcs marad meg
            oszlopok = [0.0] * (W + 1)
            for k in range(k0, k1):
                xa = int(max(0.0, (self.R_i0[k] - v0) * ppw))
                xb = int(min(float(W), (self.R_i1[k] - v0) * ppw))
                lv = self.R_lv[k]
                for x in range(xa, xb + 1):
                    if oszlopok[x] < lv:
                        oszlopok[x] = lv
            ys = [Y(v) for v in oszlopok]
            n = len(ys)
            for x in range(n):
                if x == 0 or x == n - 1 or ys[x] != ys[x - 1] or ys[x] != ys[x + 1]:
                    pontok.append((float(x), ys[x]))
            # a függőleges lépcsőket enyhén megdöntjük, hogy EKG-szerű csúcsokat kapjunk
            for i in range(len(pontok) - 1):
                xa, ya = pontok[i]
                xb, yb = pontok[i + 1]
                if xb - xa > 1.5 or ya == yb:
                    continue
                if yb < ya:      # emelkedő él: az alappont balra tolása
                    if i > 0 and pontok[i - 1][1] == ya:
                        pontok[i] = (max(pontok[i - 1][0] + 0.5, xa - 3.0), ya)
                elif i + 2 < len(pontok) and pontok[i + 2][1] == yb:   # eső él: jobbra tolás
                    pontok[i + 1] = (min(pontok[i + 2][0] - 0.5, xb + 3.0), yb)
        return pontok

    def _rajzol(self):
        self._rajz_id = None
        if self._zar:
            return
        c, T = self.canvas, self.TEMA
        try:
            W, H = c.winfo_width(), c.winfo_height()
        except tk.TclError:
            return
        if W < 40 or H < 60:
            return
        c.delete("all")
        span = self.v1 - self.v0
        ppw = W / span
        felso, ruler = 22, 24
        alap = H - ruler - 6
        magassag = max(10, alap - felso)

        def Y(szint):
            return alap - szint * magassag

        # rács + vonalzó (szószám)
        for f in (0.25, 0.5, 0.75, 1.0):
            c.create_line(0, Y(f), W, Y(f), fill=T["racs"], dash=(3, 5))
        lepes = self._szep_lepes(90.0 / ppw)
        t = math.ceil(self.v0 / lepes) * lepes
        while t <= self.v1:
            x = (t - self.v0) * ppw
            c.create_line(x, felso - 6, x, H - ruler, fill=T["racs"])
            c.create_line(x, H - ruler, x, H - ruler + 5, fill=T["halvany"])
            c.create_text(x + 3, H - ruler + 7, text=f"{int(t):,}".replace(",", " "), anchor="nw",
                          fill=T["halvany"], font=("Segoe UI", 8))
            t += lepes
        c.create_line(0, H - ruler, W, H - ruler, fill=T["racs_erosebb"])
        c.create_line(0, alap, W, alap, fill=T["racs_erosebb"])

        pontok = self._hullam_pontok(W, alap, magassag, self.v0, self.v1)
        if len(pontok) >= 2:
            lapos = [v for p in pontok for v in p]
            c.create_line(*lapos, fill=T["ragyogas"], width=6, joinstyle="round", capstyle="round")
            c.create_line(*lapos, fill=T["vonal"], width=2, joinstyle="round", capstyle="round")
        self._jelolo_rajzol()

    def _jelolo_rajzol(self):
        """A látható szövegrészek sávjai és az utolsó kattintás helye a hullámon."""
        self._jelolo_id = None
        if self._zar:
            return
        c, T = self.canvas, self.TEMA
        try:
            W, H = c.winfo_width(), c.winfo_height()
            if W < 40 or H < 60:
                return
            c.delete("jelolo")
            ppw = W / (self.v1 - self.v0)

            def X(w):
                return (w - self.v0) * ppw

            a, b = self._lathato_tartomany(0)
            x0, x1 = X(a), max(X(b), X(a) + 3)
            c.create_rectangle(x0, 3, x1, 8, fill=T["kurzor"], outline="", tags="jelolo")
            a2, b2 = self._lathato_tartomany(1)
            la = self._interpol(self._hor_j, self._hor_i, a2)
            lb = self._interpol(self._hor_j, self._hor_i, b2)
            c.create_rectangle(X(la), 10, max(X(lb), X(la) + 3), 15, fill=T["jobb_sav"],
                               outline="", tags="jelolo")
            if self._kurzor_w is not None:
                xk = X(self._kurzor_w)
                if 0 <= xk <= W:
                    c.create_line(xk, 0, xk, H - 24, fill=T["kurzor"], width=2, dash=(5, 3),
                                  tags="jelolo")
        except tk.TclError:
            pass


# ============================================================================
# LICENC- ÉS NÉVJEGY SZÖVEGEK (About ablak; ugyanez van a LICENSE / NOTICE /
# THIRD_PARTY_NOTICES.txt fájlokban is)
# ============================================================================
APACHE_LICENSE_TEXT = r"""                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
"""

ABOUT_TEXT = r"""# SzTextCompar 1.0
Text similarity and comparison analyzer

Copyright 2026 szabiz

# LICENSE OF THE ORIGINAL PROJECT CODE
The original source code of SzTextCompar is licensed under the Apache License, Version 2.0 (the "License"). You may not use this software except in compliance with the License. You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

The complete license text is shown in the "License - Apache 2.0" tab of this window and is also distributed with the program in the file LICENSE.

In short, the License grants you a perpetual, worldwide, non-exclusive, no-charge, royalty-free, irrevocable copyright license to reproduce, prepare derivative works of, publicly display, publicly perform, sublicense and distribute the software and such derivative works in source or object form, together with a patent license from each contributor (sections 2 and 3). If you redistribute the software or a derivative work, you must:
  1. give every recipient a copy of the License;
  2. mark any modified files with prominent notices stating that you changed them;
  3. retain, in the source form, all copyright, patent, trademark and attribution notices of the original work;
  4. include the readable attribution notices of the NOTICE file, if the distribution contains one (section 4).
Unless you state otherwise, any contribution intentionally submitted for inclusion is licensed under the same terms (section 5). The License does not grant permission to use the names, trademarks or product names of the licensor, except for reasonable descriptive use (section 6).

The software is provided "AS IS", WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, and the contributors are not liable for any damages arising from its use (sections 7 and 8).

IMPORTANT NOTICE ABOUT RESULTS
!!! THE APPLICATION'S RESULTS ARE SIMILARITY INDICATORS AND DO NOT BY THEMSELVES PROVE COPYING, PLAGIARISM OR COPYRIGHT INFRINGEMENT !!!

Important: the Apache License 2.0 applies to the original SzTextCompar code only. It does not replace or modify the licenses of the third-party components listed in the "Third-party notices" tab.

Soli Deo Gloria

"""

# THIRD-PARTY COMPONENTS (SUMMARY)
# The source imports only Python standard-library modules. For the actual shipped
# Windows build, this was cross-checked against BOTH the PyInstaller build log AND
# an independent, file-by-file audit of the finished dist folder (950 files, all
# attributed by SHA-256 and embedded version resources). That audit found CPython
# 3.13.14 (not 3.14.5) and PyInstaller 6.22.3 collecting OpenSSL 3.0.21, libmpdec,
# libffi, Expat, zlib 1.3.1, bzip2, XZ/liblzma, Tcl/Tk 8.6.15 (plus its bundled
# script library and IANA tzdata files) and the Microsoft Visual C++ Runtime
# 14.42.34438.0. This Python build has no _zstd module, so no Zstandard/pyzstd
# component is present. The detailed THIRD_PARTY_TEXT below reflects that audit.
#
# ALGORITHMS AND METHODS
# Simhash, Winnowing, TF-IDF, cosine similarity, Jaccard similarity, suffix-automaton
# longest-common-substring search and diff-style block matching are implemented
# independently in this application; no third-party source implementation is claimed.
#
# IMPORTANT NOTICE ABOUT RESULTS
# !!! THE APPLICATION'S RESULTS ARE SIMILARITY INDICATORS AND DO NOT BY THEMSELVES PROVE COPYING, PLAGIARISM OR COPYRIGHT INFRINGEMENT !!!

THIRD_PARTY_TEXT = r"""SzTextCompar - Third-Party Notices
=================================

PROJECT CODE
------------
SzTextCompar: Copyright 2026 szabiz.
The original SzTextCompar source code is licensed under the Apache License,
Version 2.0. See the project's LICENSE and NOTICE files.

The application source itself imports only Python standard-library modules;
no PyPI package is imported by the application source. The executable is,
however, built with CPython and PyInstaller, so the released distribution
contains components from those projects and from the native libraries used
by the exact Python build.

BINARY BUILD IDENTIFICATION FOR THIS RELEASE
---------------------------------------------
  Python:            3.13.14 (Windows Store / python.org build, 64-bit)
  PyInstaller:       6.22.3  (contrib hooks: 2026.7)
  Build OS:          Windows 11, OS build 26200, x64
  Packaging:         PyInstaller onedir (COLLECT)
  UPX:               not used (not available in the build environment)
  Dist folder audit: 950 files total, all 950 successfully attributed to a
                      known component (0 unclassified) - see below.

IMPORTANT: This notice is based on two independent, matching sources for this
exact release: (1) the PyInstaller build's own analysis/debug log, and (2) a
separate, file-by-file audit of the finished dist folder that checked every
one of the 950 shipped files individually (by SHA-256 hash and, where
present, the file's embedded FileVersion/CompanyName/LegalCopyright resource
strings). Both sources agree. Earlier drafts of this notice, produced before
the actual build existed, incorrectly assumed Python 3.14.5 and a bundled
Zstandard/_zstd module; the real build uses Python 3.13.14, which has no
_zstd module, and no Zstandard/pyzstd component is present in the shipped
files. That assumption has been removed below.

Non-system native files (DLL/PYD) collected for this build:

  python313.dll        VCRUNTIME140.dll      select.pyd
  _multiprocessing.pyd  pyexpat.pyd           _ssl.pyd
  libcrypto-3.dll       libssl-3.dll          _decimal.pyd
  _hashlib.pyd          _socket.pyd           _lzma.pyd
  _bz2.pyd              _ctypes.pyd           libffi-8.dll
  _queue.pyd            unicodedata.pyd       _elementtree.pyd
  _tkinter.pyd          tk86t.dll             tcl86t.dll
  zlib1.dll

In addition, two large sets of non-binary, third-party *data* files are
bundled because Tcl/Tk requires them (listed in detail in section 11 below):
609 IANA time-zone data files and 317 Tcl/Tk standard script-library files
(.tcl/.tm/.msg/.enc). Together with the 22 native files above, the project's
own base_library.zip (compiled standard-library bytecode) and the
application executable itself, these account for all 950 files in the dist
folder.

select.pyd, _multiprocessing.pyd, _queue.pyd and _socket.pyd are not used
directly by SzTextCompar's own code; PyInstaller collected them because
Python's concurrent.futures/threading machinery imports them internally.

Windows system DLLs such as KERNEL32.dll, ADVAPI32.dll, USER32.dll,
WS2_32.dll, bcrypt.dll, VERSION.dll and the related api-ms-win-* components
are not bundled third-party application files; PyInstaller explicitly
skipped them as system dependencies supplied by Windows itself, and they are
not listed as application-bundled third-party libraries in this notice.

1. PYTHON SOFTWARE FOUNDATION / CPYTHON
----------------------------------------
Component:  python313.dll (the CPython interpreter), base_library.zip
Version:    3.13.14
Licence:    Python Software Foundation License Version 2
Copyright:  Copyright (c) 2001-2024 Python Software Foundation. Copyright (c)
            2000 BeOpen.com. Copyright (c) 1995-2001 CNRI. Copyright (c)
            1991-1995 SMC. (exact string embedded in the shipped binaries)

Python software is licensed under the Python Software Foundation License
Version 2. This copyright and license text must be retained when CPython is
redistributed. The Python distribution also incorporates the separately
licensed components listed in the sections below (all of them confirmed
present, by exact file, in this release's dist folder).

Official Python license and incorporated-software acknowledgements:
  https://docs.python.org/3/license.html

2. OPENSSL
----------
Component:  libcrypto-3.dll, libssl-3.dll (used by _ssl.pyd and _hashlib.pyd)
Version:    3.0.21
Licence:    Apache License 2.0
Copyright:  Copyright 1998-2026 The OpenSSL Authors. All rights reserved.
            (exact string embedded in the shipped DLLs)

CPython's _hashlib.pyd additionally incorporates HACL* (MIT licensed) and a
public-domain/CC0 BLAKE2 reference implementation for some hash algorithms,
alongside OpenSSL, per Python's own license documentation.
  https://openssl-library.org/source/license/index.html
  https://docs.python.org/3/license.html

3. LIBMPDEC
-----------
Component:  _decimal.pyd
Licence:    BSD 2-Clause (Simplified BSD)

Python's _decimal extension statically incorporates libmpdec. Its copyright
notice must be retained.
  https://www.bytereef.org/mpdecimal/

4. LIBFFI
---------
Component:  _ctypes.pyd, libffi-8.dll
Licence:    MIT-style licence

The libffi component used by CPython's ctypes module is MIT licensed. Its
copyright and permission notice must be retained.
  https://github.com/libffi/libffi/blob/master/LICENSE

5. EXPAT
--------
Component:  pyexpat.pyd, _elementtree.pyd (Python's Expat-based XML tree module)
Licence:    MIT License

CPython's pyexpat extension, and the ElementTree implementation built on top
of it, incorporate Expat. Its copyright and permission notice must be
retained.
  https://libexpat.github.io/

6. UNICODE CHARACTER DATABASE
-----------------------------
Component:  unicodedata.pyd
Licence:    Python Software Foundation License / Unicode License

CPython's unicodedata module contains an extract of the Unicode Character
Database (UCD). The applicable Unicode copyright and permission notice must
be retained.
  https://docs.python.org/3/license.html

7. ZLIB
--------
Component:  zlib1.dll
Version:    1.3.1
Licence:    zlib License
Copyright:  (C) 1995-2022 Jean-loup Gailly & Mark Adler (exact string
            embedded in the shipped DLL)

SzTextCompar also directly uses Python's zlib module for the "create files"
skill's PNG output. In addition, PyInstaller's own Windows bootloader
statically contains zlib source; this is a second, independent reason the
zlib notice applies to the executable.
  https://zlib.net/zlib_license.html

8. BZIP2
--------
Component:  _bz2.pyd
Licence:    bzip2 License (BSD-style)

Corresponds to Python's bz2 support and the bzip2 library. The applicable
copyright/license notice must be retained.
  https://sourceware.org/bzip2/

9. XZ / LIBLZMA
---------------
Component:  _lzma.pyd
Licence:    Public Domain / 0BSD

Corresponds to Python's lzma support and liblzma/XZ. Public-domain / 0BSD
components carry no mandatory notice, but are listed here for completeness.
  https://github.com/tukaani-project/xz

10. MICROSOFT VISUAL C++ RUNTIME
--------------------------------
Component:  VCRUNTIME140.dll
Version:    14.42.34438.0
Licence:    Microsoft's redistributable runtime terms
Copyright:  (c) Microsoft Corporation. All rights reserved.

This is Microsoft's Visual C++ runtime component used by the Python
interpreter and its native extensions. Redistribution is governed by
Microsoft's applicable runtime terms, not by an OSI licence.
  https://learn.microsoft.com/cpp/windows/redistributing-visual-cpp-files

11. TCL/TK (INTERPRETER, PYTHON BINDING, SCRIPT LIBRARY AND TIME-ZONE DATA)
----------------------------------------------------------------------------
Component:  _tkinter.pyd, tcl86t.dll, tk86t.dll
Version:    8.6.15
Licence:    Tcl/Tk License (BSD-style)
Copyright:  Copyright (c) 1987-2022 Regents of the University of California
            and other parties (exact string embedded in the shipped DLLs)

SzTextCompar uses tkinter for its entire graphical user interface. Besides
the two DLLs and the Python binding module above, the dist folder also ships
two further sets of files that are part of the same Tcl/Tk distribution and
carry the same licence:

  - 317 Tcl/Tk standard script-library files (.tcl/.tm/.msg/.enc), under
    _internal\\tcl8\\, _internal\\_tcl_data\\ and _internal\\_tk_data\\ - the
    Tcl/Tk scripts, message catalogues and encodings the interpreter loads
    at runtime.
  - 609 IANA Time Zone Database (tzdata) files, under
    _internal\\_tcl_data\\tzdata\\ - bundled by Tcl itself so that its
    "clock" command has time-zone data independent of the host OS. The IANA
    Time Zone Database is public domain.
      https://www.iana.org/time-zones

  https://www.tcl.tk/software/tcltk/license.html

12. PYINSTALLER
---------------
Component:  SzTextCompar.exe (bootloader + the frozen application)
Licence:    GPL-2.0-or-later WITH the PyInstaller Bootloader Exception

PyInstaller 6.22.3 (contrib hooks 2026.7) is the build/packaging tool. Its
Windows bootloader is compiled into SzTextCompar.exe, and PyInstaller's
Python bootstrap/runtime-hook code is placed into the generated application
archive.

PyInstaller's own code is GPL-2.0-or-later; certain PyInstaller files are
Apache License 2.0. The official PyInstaller license page states that the
Bootloader Exception explicitly permits the generated application (the
bootloader plus the frozen program) to be distributed under the
application's own licence, subject to the licences of the application's own
dependencies, and that PyInstaller's licence file and acknowledgement are
not required to be shipped with the generated application.

SzTextCompar nevertheless lists PyInstaller here for transparency.
  https://pyinstaller.org/en/stable/license.html

13. PYINSTALLER BUILD-TIME PACKAGES
-----------------------------------
The build environment contains PyInstaller and pyinstaller-hooks-contrib.
Those packages are build-time tooling: their hook source files are used by
PyInstaller during analysis and are not, by themselves, evidence that the
corresponding package source code is embedded in the final application.
Packages used only for build-time analysis are not application runtime
dependencies merely because they appear in the build virtual environment.

14. PYTHON STANDARD-LIBRARY MODULES USED BY THE APPLICATION SOURCE
--------------------------------------------------------------------
The application's own Python source uses standard-library modules, including:
  tkinter, difflib, re, string, os, json, hashlib, concurrent.futures,
  pathlib, collections, math, threading, html, time, io, struct, zlib,
  zipfile, posixpath, urllib.parse, html.parser, xml.etree.ElementTree,
  xml.sax.saxutils, bisect, webbrowser.

These modules are part of CPython; they are not separate PyPI dependencies
of SzTextCompar. Some of them cause the native components listed above
(section 1-11) to be collected by PyInstaller.

15. PROJECT-ORIGINAL ARTWORK
----------------------------
The application icon/artwork is project-original material, built from
geometric shapes (see make_icon.py). No third-party font file and no
third-party image file is intentionally bundled by the source. System fonts
such as Segoe UI, Consolas, Arial and Courier New are requested from Windows
and are not redistributed by SzTextCompar.

16. WORD LISTS
--------------
MAGYAR_STOPSZAVAK and ANGOL_STOPSZAVAK are short lists of very common
Hungarian and English function words (for example "a", "az", "hogy" / "the",
"of", "and"). The program picks the list that matches the language of the
compared texts. A list of common words is factual data and is not
third-party source code.

17. ALGORITHMS AND METHODS
--------------------------
Simhash, Winnowing, TF-IDF, cosine similarity, Jaccard similarity,
suffix-automaton longest-common-substring search and diff-style block
matching are implemented independently in SzTextCompar. The mathematical
methods themselves are not third-party software packages, and no
third-party source implementation is claimed or intentionally copied for
them.

18. RELEASE REQUIREMENT
-----------------------
For every public binary release, distribute this notice and the
corresponding THIRD_PARTY_LICENSES.txt file together with the application,
and retain the exact copyright/licence material embedded in
the bundled CPython, OpenSSL, Tcl/Tk and Microsoft Visual C++ Runtime
components for that specific build. Do not replace exact copyright notices
with generic names when the upstream license requires the notice to be
reproduced verbatim.

The version numbers in this notice (Python 3.13.14, PyInstaller 6.22.3,
OpenSSL 3.0.21, Tcl/Tk 8.6.15, zlib 1.3.1, Microsoft Visual C++ Runtime
14.42.34438.0) are tied to this exact release. For a future build using a
different Python version, PyInstaller version, spec file, or Python
distribution, regenerate this inventory from the new build log and a fresh
file-by-file audit of the resulting dist directory - do not simply assume
the same versions carried over from a previous release.

This notice is a technical licensing inventory, not a legal opinion.
"""


# ============================================================================
# PROGRAMIKON (SzTc) - a make_icon.py-val geometriai alakzatokból rajzolt, saját
# ábra (nem használ betűtípust vagy külső képet). PNG méretek: 32, 64, 128 px.
# Az exe ikonja a SzTc.ico fájl (PyInstaller: --icon SzTc.ico).
# ============================================================================
APP_ICON_PNG_B64 = [
"""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
Q25sjrY/dGA7qyX385pO1cqx9wqdsWTHJpHPmexjCPsYwqYAX3GUtkaU9lRInZniwIsHSJ1dh87lyY6uQ6cSJM9MUv53heYfNZB/
rwTmcx4XDrrfrWDzunoVi1TPReRYnaNCobzT0v5cnkQ/Q+o0Q69v9USSin3PHCR9boY+UxuJ2mPKuyI+/ksXpZ2WzPkBif4B3vpj
/SqoKjGNEaOtLWndsdIeV3CKAp1JE7U7Sjss+a0dJJo1vpLAOyHsk6D1wU9QyQQqGRL2VhS3WwpbLIeV2VHCUKUSiMFKryvvaRGl
B4IVjon1SNhqMkwJPvL42CFaETTGiPZU9hhUUuGtr0F3IgnvPWjvnd2pRKlFEiQVXsVVxhzHaqzFKyTQqFSAhJqoPaSyN0QSBu8U
n2bVCX15FUuQVKLUImXDaJ6PK5tUMhsgEiHKI4oT2hHOVGhQyaAW5P/4T5RHJFLJbODjyiYbRvMEoPc19w6C5PNKB8O9jfDOfjFv
U6URHeBstAFKE9tevH+HZtYslX9y9sG65osXS0JXvJJmUDkEdRLfiR7REUptw/Oo64xu2v/q7P3MmqX+A8LbpPGKBGAGAAAAAElF
TkSuQmCC""",
"""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""",
]


class SzTextCompar(tk.Tk):
    def __init__(self):
        super().__init__()
        self._ikon_beallitasa()
        self.title(tr("SzTextCompar 1.0 - Szöveghasonlóság-elemző"))
        self.geometry("1350x850")
        self.minsize(950, 600)

        self.fajl1_utvonal = None
        self.fajl2_utvonal = None
        self.utolso_mappa = None

        self.elozmeny_stack = []
        self._tree_sort_state = {}

        # Közös betűtípus-objektum a bal/jobb szövegmezőkhöz: egy Tk Font példány
        # átméretezése minden vele beállított widgeten azonnal érvényesül, így a
        # nagyító/kicsinyítő gombok mindkét panelt egyszerre és élőben állítják.
        self.SZOVEG_BETUMERET_ALAP = 11
        self.SZOVEG_BETUMERET_MIN, self.SZOVEG_BETUMERET_MAX = 7, 28
        self.szoveg_font = tkfont.Font(family="Consolas", size=self.SZOVEG_BETUMERET_ALAP)

        self._epitsd_felulet()
        self._nyelv_menu_letrehozasa()

    def _nyelv_menu_letrehozasa(self):
        menubar = tk.Menu(self)
        nyelvmenu = tk.Menu(menubar, tearoff=0)
        nyelvmenu.add_command(label=tr("Magyar"), command=lambda: self._nyelvvaltasa("hu"))
        nyelvmenu.add_command(label=tr("English"), command=lambda: self._nyelvvaltasa("en"))
        menubar.add_cascade(label=tr("Nyelv"), menu=nyelvmenu)
        menubar.add_command(label=tr("Szín"), command=self._szin_ablak)
        menubar.add_command(label=tr("Névjegy"), command=self._about_megjelenitese)
        self.config(menu=menubar)

    def _ikon_beallitasa(self):
        """Ablak- és tálcaikon (bal felső sarok) a beágyazott PNG-kből; minden további ablak is ezt kapja."""
        try:
            self._ikon_kepek = [tk.PhotoImage(data="".join(b.split())) for b in APP_ICON_PNG_B64]
            self.iconphoto(True, *self._ikon_kepek)
        except tk.TclError:
            pass

    def _betumeret_valtas(self, delta):
        """A bal/jobb szövegmezők közös betűméretét nagyítja/kicsinyíti (mindkét panelt
        egyszerre, mivel egy közös Tk Font objektumot használnak)."""
        uj_meret = max(self.SZOVEG_BETUMERET_MIN, min(self.SZOVEG_BETUMERET_MAX,
                                                        self.szoveg_font.cget("size") + delta))
        self.szoveg_font.configure(size=uj_meret)
        for w in (getattr(self, "text1", None), getattr(self, "text2", None)):
            if w is not None:
                self.after_idle(lambda w=w: self._frissit_sorszamok(w))

    def _betumeret_visszaallitas(self):
        self.szoveg_font.configure(size=self.SZOVEG_BETUMERET_ALAP)
        for w in (getattr(self, "text1", None), getattr(self, "text2", None)):
            if w is not None:
                self.after_idle(lambda w=w: self._frissit_sorszamok(w))

    def _szinek_alkalmazasa(self):
        """A mentett/megadott színek élő alkalmazása a főablak szövegmezőin."""
        for t in (self.text1, self.text2):
            t.tag_configure("egyezes", background=SZINEK["egyezes"], foreground=szin_kontraszt(SZINEK["egyezes"]))
            t.tag_configure("hdiff_kijelolt", background=SZINEK["hdiff_kijelolt"],
                            foreground=szin_kontraszt(SZINEK["hdiff_kijelolt"]))
            for tag in t.tag_names():
                m = re.fullmatch(r"(egyez|hdiff)_(\d+)", tag)
                if not m:
                    continue
                pal = SZINEK["paletta"] if m.group(1) == "egyez" else SZINEK["diff_paletta"]
                szin = pal[(int(m.group(2)) - 1) % len(pal)]
                t.tag_configure(tag, background=szin, foreground=szin_kontraszt(szin))
            if "egyez_kijelolt" in t.tag_names():
                t.tag_configure("egyez_kijelolt", background=SZINEK["kijelolt_hatter"],
                                foreground=SZINEK["kijelolt_szoveg"])
                t.tag_raise("egyez_kijelolt")
            if "hdiff_kijelolt" in t.tag_names():
                t.tag_raise("hdiff_kijelolt")

    def _szin_ablak(self):
        """Felugró ablak, ahol a találatok színei tetszés szerint beállíthatók."""
        from tkinter import colorchooser
        regi = getattr(self, "_szin_win", None)
        if regi is not None and regi.winfo_exists():
            regi.lift(); regi.focus_force()
            return
        win = self._szin_win = tk.Toplevel(self)
        win.title(tr("Színek – találatok"))
        win.transient(self)
        win.resizable(False, False)
        munka = {k: (list(v) if isinstance(v, list) else v) for k, v in SZINEK.items()}
        frissitok = []

        def kocka(szulo, kulcs, idx=None, felirat="Aa 123", szoveg_szin=False):
            def ertek():
                return munka[kulcs][idx] if idx is not None else munka[kulcs]

            l = tk.Label(szulo, text=felirat, width=9, relief="solid", bd=1, cursor="hand2",
                         font=("Segoe UI", 10, "bold"), pady=4)

            def rajz():
                e = ertek()
                if szoveg_szin:
                    l.configure(bg=munka["kijelolt_hatter"], fg=e)
                else:
                    l.configure(bg=e, fg=szin_kontraszt(e))

            def valaszt(_=None):
                uj = colorchooser.askcolor(color=ertek(), parent=win, title=tr("Szín kiválasztása"))
                if uj and uj[1]:
                    hexa = uj[1].lower()
                    if idx is not None:
                        munka[kulcs][idx] = hexa
                    else:
                        munka[kulcs] = hexa
                    for f in frissitok:
                        f()

            l.bind("<Button-1>", valaszt)
            frissitok.append(rajz)
            rajz()
            return l

        keret = ttk.Frame(win, padding=12)
        keret.pack(fill="both", expand=True)
        ttk.Label(keret, text=tr("Kattints egy színre a módosításhoz.")).pack(anchor="w", pady=(0, 8))

        for cim, kulcs in (("Egyezések vizuális nézete (8 szín, sorban ismétlődve)", "paletta"),
                           ("Hagyományos diff – jelentős egyező szakaszok (8 szín)", "diff_paletta")):
            lf = ttk.LabelFrame(keret, text=" " + tr(cim) + " ", padding=8)
            lf.pack(fill="x", pady=4)
            for i in range(8):
                kocka(lf, kulcs, i, felirat=f" {i + 1} ").grid(row=0, column=i, padx=3)

        lf = ttk.LabelFrame(keret, text=" " + tr("Kijelölés és általános kiemelés") + " ", padding=8)
        lf.pack(fill="x", pady=4)
        sorok = (("Kijelölt egyezés háttere", "kijelolt_hatter", False),
                 ("Kijelölt egyezés szövege", "kijelolt_szoveg", True),
                 ("Kijelölt diff blokk háttere", "hdiff_kijelolt", False),
                 ("Rövid egyezés kiemelése", "egyezes", False))
        for r, (cim, kulcs, szoveg_szin) in enumerate(sorok):
            ttk.Label(lf, text=tr(cim)).grid(row=r, column=0, sticky="w", padx=(0, 16), pady=2)
            kocka(lf, kulcs, szoveg_szin=szoveg_szin).grid(row=r, column=1, pady=2)

        lf = ttk.LabelFrame(keret, text=" " + tr("EKG (hullámforma) ablak") + " ", padding=8)
        lf.pack(fill="x", pady=4)
        for r, (cim, kulcs) in enumerate((("Hullám vonala", "ekg_vonal"), ("Egyező szöveg kiemelése", "ekg_szoveg"))):
            ttk.Label(lf, text=tr(cim)).grid(row=r, column=0, sticky="w", padx=(0, 16), pady=2)
            kocka(lf, kulcs).grid(row=r, column=1, pady=2)

        def alkalmaz():
            for k, v in munka.items():
                SZINEK[k] = list(v) if isinstance(v, list) else v
            szinek_mentese()
            self._szinek_alkalmazasa()

        def alap():
            for k, v in SZIN_ALAP.items():
                munka[k] = list(v) if isinstance(v, list) else v
            for f in frissitok:
                f()

        gombok = ttk.Frame(keret)
        gombok.pack(fill="x", pady=(10, 0))
        ttk.Button(gombok, text=tr("Alapértelmezett"), command=alap).pack(side="left")
        ttk.Button(gombok, text=tr("Mégse"), command=win.destroy).pack(side="right")
        ttk.Button(gombok, text=tr("OK"), command=lambda: (alkalmaz(), win.destroy())).pack(side="right", padx=6)
        ttk.Button(gombok, text=tr("Alkalmaz"), command=alkalmaz).pack(side="right")
        win.bind("<Escape>", lambda e: win.destroy())
        win.focus_force()

    def _about_megjelenitese(self):
        """About: program, Apache License 2.0 (teljes szöveg) és harmadik fél megjegyzések - csak angolul."""
        regi = getattr(self, "_about_win", None)
        if regi is not None and regi.winfo_exists():
            regi.lift(); regi.focus_force()
            return
        win = self._about_win = tk.Toplevel(self)
        win.title("About")
        win.geometry("860x720")
        win.minsize(640, 480)
        win.transient(self)

        nb = ttk.Notebook(win)
        nb.pack(fill="both", expand=True, padx=10, pady=(10, 4))
        for cim, tartalom, monospace in (("About", ABOUT_TEXT, False),
                                         ("License - Apache 2.0", APACHE_LICENSE_TEXT, True),
                                         ("Third-party notices", THIRD_PARTY_TEXT, True)):
            keret = ttk.Frame(nb)
            nb.add(keret, text=cim)
            txt = tk.Text(keret, wrap="word" if not monospace else "none", padx=12, pady=10,
                          font=("Consolas", 10) if monospace else ("Segoe UI", 10))
            vsb = ttk.Scrollbar(keret, orient="vertical", command=txt.yview)
            txt.configure(yscrollcommand=vsb.set)
            if monospace:
                hsb = ttk.Scrollbar(keret, orient="horizontal", command=txt.xview)
                txt.configure(xscrollcommand=hsb.set)
                hsb.pack(side="bottom", fill="x")
            vsb.pack(side="right", fill="y")
            txt.pack(side="left", fill="both", expand=True)
            txt.tag_configure("cim", font=("Segoe UI", 11, "bold"), spacing1=10, spacing3=3)
            for sor in tartalom.split("\n"):
                if not monospace and sor.startswith("# "):
                    txt.insert("end", sor[2:] + "\n", "cim")
                else:
                    txt.insert("end", sor + "\n")
            txt.configure(state="disabled")
        ttk.Button(win, text="Close", command=win.destroy).pack(pady=(4, 12))
        win.bind("<Escape>", lambda e: win.destroy())

    def _nyelvvaltasa(self, lang):
        if lang == CURRENT_LANGUAGE:
            return
        # A nyelvváltásnál újraépítjük a GUI-t; a fájlok és a szövegek megmaradnak.
        s1 = self.text1.get("1.0", "end-1c") if hasattr(self, "text1") else ""
        s2 = self.text2.get("1.0", "end-1c") if hasattr(self, "text2") else ""
        f1, f2 = self.fajl1_utvonal, self.fajl2_utvonal
        set_language(lang)
        for child in list(self.winfo_children()):
            child.destroy()
        self.elozmeny_stack = []
        self.fajl1_utvonal, self.fajl2_utvonal = f1, f2
        self._epitsd_felulet()
        self._nyelv_menu_letrehozasa()
        if s1:
            self.text1.insert("1.0", s1)
        if s2:
            self.text2.insert("1.0", s2)
        if f1 or f2:
            self.cimke1_var.set(f"{tr(tr("Bal fájl"))}: {Path(f1).name if f1 else tr(tr("(nincs betöltve)"))}")
            self.cimke2_var.set(f"{tr(tr("Jobb fájl"))}: {Path(f2).name if f2 else tr(tr("(nincs betöltve)"))}")

    def _allapot_mentes(self):
        s1 = self.text1.get("1.0", "end-1c")
        s2 = self.text2.get("1.0", "end-1c")
        self.elozmeny_stack.append((s1, s2))
        if len(self.elozmeny_stack) > 20:
            self.elozmeny_stack.pop(0)

    def visszalepes(self):
        if not self.elozmeny_stack:
            messagebox.showinfo(tr("Vissza"), "Nincs több visszavonható lépés.")
            return
        s1, s2 = self.elozmeny_stack.pop()
        self.text1.delete("1.0", "end")
        self.text1.insert("1.0", s1)
        self.text2.delete("1.0", "end")
        self.text2.insert("1.0", s2)
        self.statusz_var.set(tr("Sikeres visszalépés az előző állapotba."))

    def _epitsd_felulet(self):
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(side="top", fill="both", expand=True)

        self.ful_ketfajl = ttk.Frame(self.notebook)
        self.notebook.add(self.ful_ketfajl, text="  Kétfájlos Összehasonlítás & Szöveghasonlóság  ")
        self._epitsd_ketfajl_nezet(self.ful_ketfajl)

        self.ful_mappa = ttk.Frame(self.notebook)
        self.notebook.add(self.ful_mappa, text="  Mappa Mátrix – Szöveghasonlóság  ")
        self._epitsd_mappa_nezet(self.ful_mappa)

        # A háttérszámítások közben középen jelenik meg; nem függ a jobb alsó
        # sarokba szorított progressbartól, ezért mindkét fülön jól látható.
        self._mozgasjelzo_aktiv = False
        self._mozgasjelzo_id = None
        self._mozgasjelzo_keret = tk.Frame(self.notebook, background="#fff7d6",
                                           highlightbackground="#c99a23", highlightthickness=1,
                                           padx=24, pady=16)
        self._mozgasjelzo_icon = tk.Label(self._mozgasjelzo_keret, text="⏳",
                                          font=("Segoe UI Emoji", 30), background="#fff7d6")
        self._mozgasjelzo_icon.pack()
        self._mozgasjelzo_szoveg = tk.Label(self._mozgasjelzo_keret, text=tr("Számítás folyamatban…"),
                                            font=("TkDefaultFont", 11, "bold"), background="#fff7d6")
        self._mozgasjelzo_szoveg.pack(pady=(5, 0))

        statusz_keret = ttk.Frame(self, padding=6, relief="sunken")
        statusz_keret.pack(side="bottom", fill="x")
        
        self.statusz_var = tk.StringVar(value=tr("Nyiss meg két fájlt, vagy válassz ellenőrzési típust."))
        ttk.Label(statusz_keret, textvariable=self.statusz_var,
                  font=("TkDefaultFont", 10, "bold")).pack(side="left", padx=5)

    def _mozgasjelzo_inditasa(self, uzenet="Számítás folyamatban…"):
        """Középre helyezett, egyszerűen animált várakozásjelző indítása."""
        self._mozgasjelzo_aktiv = True
        self._mozgasjelzo_szoveg.configure(text=uzenet)
        self._mozgasjelzo_keret.place(relx=0.5, rely=0.5, anchor="center")
        self._mozgasjelzo_keret.lift()
        self._mozgasjelzo_lepes(0)

    def _mozgasjelzo_lepes(self, index):
        if not self._mozgasjelzo_aktiv:
            return
        self._mozgasjelzo_icon.configure(text=("⏳", "⌛", "⏳", "⌛")[index % 4])
        self._mozgasjelzo_id = self.after(350, lambda: self._mozgasjelzo_lepes(index + 1))

    def _mozgasjelzo_leallitasa(self):
        self._mozgasjelzo_aktiv = False
        if self._mozgasjelzo_id is not None:
            try:
                self.after_cancel(self._mozgasjelzo_id)
            except tk.TclError:
                pass
            self._mozgasjelzo_id = None
        self._mozgasjelzo_keret.place_forget()

    def _epitsd_ketfajl_nezet(self, szulo):
        eszkoztar1 = ttk.Frame(szulo, padding=(6, 6, 6, 2))
        eszkoztar1.pack(side="top", fill="x")

        ttk.Button(eszkoztar1, text=tr("⬅ Vissza"), command=self.visszalepes).pack(side="left", padx=4)
        ttk.Separator(eszkoztar1, orient="vertical").pack(side="left", fill="y", padx=6)

        ttk.Button(eszkoztar1, text=tr("Bal fájl megnyitása..."),
                   command=lambda: self.fajl_megnyitas(1)).pack(side="left", padx=4)
        ttk.Button(eszkoztar1, text=tr("Jobb fájl megnyitása..."),
                   command=lambda: self.fajl_megnyitas(2)).pack(side="left", padx=4)
        
        ttk.Separator(eszkoztar1, orient="vertical").pack(side="left", fill="y", padx=6)
        
        ttk.Button(eszkoztar1, text=tr("Bal mentése másként..."),
                   command=lambda: self.fajl_mentes(1)).pack(side="left", padx=4)
        ttk.Button(eszkoztar1, text=tr("Jobb mentése másként..."),
                   command=lambda: self.fajl_mentes(2)).pack(side="left", padx=4)

        ttk.Separator(eszkoztar1, orient="vertical").pack(side="left", fill="y", padx=6)

        betumeret_keret = ttk.Frame(eszkoztar1)
        betumeret_keret.pack(side="left")
        for szoveg, parancs in (("🔍−", lambda: self._betumeret_valtas(-1)),
                                ("🔍", self._betumeret_visszaallitas),
                                ("🔍+", lambda: self._betumeret_valtas(1))):
            ttk.Button(betumeret_keret, text=szoveg, command=parancs).pack(side="left", padx=1)

        eszkoztar2 = ttk.Frame(szulo, padding=(6, 2, 6, 6))
        eszkoztar2.pack(side="top", fill="x")

        mod_keret = ttk.LabelFrame(eszkoztar2, text=tr("Elemzési mód"), padding=(6, 3))
        mod_keret.pack(side="left", padx=(2, 6))

        self.ellenorzes_tipus_var = tk.StringVar(value=tr(tr("Winnowing Ujjlenyomat (szövegegyezés-vizsgálat)")))
        tipusok = [
            tr("Winnowing Ujjlenyomat (szövegegyezés-vizsgálat)"),
            tr("TF-IDF Súlyozott Tartalmi Elemzés (Precíz Cosine)"),
            tr("Mondatritmus & Struktúra (Parafrázis szűrő)"),
            tr("Hagyományos Diff (Karakter/Sor)"),
            tr("N-gram kifejezés-egyezés"),
            tr("Szókészlet (Cosine) hasonlóság"),
            tr("Jaccard-hasonlóság (Halmaz alapú)"),
            tr("Stilisztikai elemzés (Szókincs gazdagság)"),
            tr("Simhash Ujjlenyomat (Nyelvfüggetlen, gyors)"),
        ]
        self.tipus_combo = ttk.Combobox(mod_keret, textvariable=self.ellenorzes_tipus_var,
                                        values=tipusok, state="readonly", width=38)
        self.tipus_combo.pack(side="left", padx=4)
        self.tipus_combo.bind(
        "<<ComboboxSelected>>",
        self._frissit_diff_opciok
        )

        ttk.Button(mod_keret, text=tr("Indítás"), command=self.osszehasonlitas,
                   style="Accent.TButton").pack(side="left", padx=(5, 0))
        
        # Összesítő tábla gomb
        ttk.Button(eszkoztar2, text=tr("📋 Összesítő Tábla & Hasonlósági Index"), 
                   command=self.minden_elemzes_ablak, style="Accent.TButton").pack(side="left", padx=5)
        ttk.Button(eszkoztar2, text=tr("📊 Részletes vizualizáció"),
                   command=self.reszletes_vizualizacio_ablak).pack(side="left", padx=5)

        ttk.Separator(eszkoztar2, orient="vertical").pack(side="left", fill="y", padx=6)

        self.diff_opcio_keret = ttk.LabelFrame(
        eszkoztar2,
        text="Diff beállítások"
        )
        self.diff_opcio_keret.pack(side="left", padx=6)

        self.szokoz_ki_var = tk.BooleanVar(value=False)
        self.irasjel_ki_var = tk.BooleanVar(value=False)

        self.chk_szokoz = ttk.Checkbutton(
            self.diff_opcio_keret,
            text="Szóközök mellőzése",
            variable=self.szokoz_ki_var
        )
        self.chk_szokoz.pack(side="left", padx=2)

        self.chk_irasjel = ttk.Checkbutton(
            self.diff_opcio_keret,
            text="Írásjelek mellőzése",
            variable=self.irasjel_ki_var
        )
        self.chk_irasjel.pack(side="left", padx=2)

        self.szinkron_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(eszkoztar2, text=tr("Szinkron görgetés"), variable=self.szinkron_var).pack(side="left", padx=6)

        eszkoztar3 = ttk.Frame(szulo, padding=(6, 2, 6, 6))
        eszkoztar3.pack(side="top", fill="x")

        ttk.Button(eszkoztar3, text=tr("Bal: időbélyeg törlés"),
                   command=lambda: self.idobelyeg_torles(1)).pack(side="left", padx=4)
        ttk.Button(eszkoztar3, text=tr("Jobb: időbélyeg törlés"),
                   command=lambda: self.idobelyeg_torles(2)).pack(side="left", padx=4)
        ttk.Separator(eszkoztar3, orient="vertical").pack(side="left", fill="y", padx=6)
        ttk.Button(eszkoztar3, text=tr("Sorok szinkronizálása (Diff blokk)"),
                   command=self.sorok_szinkronizalasa).pack(side="left", padx=4)
        ttk.Separator(eszkoztar3, orient="vertical").pack(side="left", fill="y", padx=6)
        ttk.Button(eszkoztar3, text=tr("🌐 HTML Riport"),
                   command=self.html_riport_general).pack(side="left", padx=4)
        ttk.Button(eszkoztar3, text=tr("🔎 Egyezések vizuális nézete"),
                   command=self.vizualis_egyezesek).pack(side="left", padx=4)
        ttk.Button(eszkoztar3, text=tr("📈 Teljes képernyő (EKG)"),
                   command=self.teljes_kepernyo_ekg).pack(side="left", padx=4)

        self.hdiff_nav_szeparator = ttk.Separator(eszkoztar3, orient="vertical")
        self.hdiff_nav_keret = ttk.Frame(eszkoztar3)
        ttk.Button(self.hdiff_nav_keret, text=tr("◀ Előző egyezés"),
                   command=self._hagyomanyos_diff_elozo).pack(side="left", padx=4)
        ttk.Button(self.hdiff_nav_keret, text=tr("Következő egyezés ▶"),
                   command=self._hagyomanyos_diff_kovetkezo).pack(side="left", padx=4)
        self.hdiff_szamlalo_var = tk.StringVar(value="")
        ttk.Label(self.hdiff_nav_keret, textvariable=self.hdiff_szamlalo_var).pack(side="left", padx=6)

        fo_keret = ttk.Frame(szulo)
        fo_keret.pack(side="top", fill="both", expand=True, padx=6, pady=4)
        self._fo_keret = fo_keret
        fo_keret.columnconfigure(0, weight=1)
        fo_keret.columnconfigure(1, weight=1)
        fo_keret.columnconfigure(2, weight=0, minsize=0)
        fo_keret.rowconfigure(1, weight=1)
        self._egyezesi_panel = None
        self._hagyomanyos_diff_blokkok = []
        self._hdiff_aktiv_index = -1
        self._aktiv_diff_panel = None

        self.cimke1_var = tk.StringVar(value=tr(tr("Bal fájl: (nincs betöltve)")))
        self.cimke2_var = tk.StringVar(value=tr(tr("Jobb fájl: (nincs betöltve)")))
        ttk.Label(fo_keret, textvariable=self.cimke1_var, font=("TkDefaultFont", 9, "bold")
                  ).grid(row=0, column=0, sticky="w", padx=4)
        ttk.Label(fo_keret, textvariable=self.cimke2_var, font=("TkDefaultFont", 9, "bold")
                  ).grid(row=0, column=1, sticky="w", padx=4)

        self.text1 = self._keszits_szoveg_dobozt(fo_keret, 0)
        self.text2 = self._keszits_szoveg_dobozt(fo_keret, 1)

        self.text1.vbar.configure(command=self._szinkron_yview_factory(self.text1, self.text2))
        self.text2.vbar.configure(command=self._szinkron_yview_factory(self.text2, self.text1))

        # Nyomon követjük, melyik panelt nézi/használja épp a felhasználó, hogy az
        # Előző/Következő egyezés gombok (és a kattintásos ugrás) csak a SZEMKÖZTI
        # (a másik) panelt görgessék - azt, amit épp néz, ne mozdítsuk el alóla.
        self.text1.bind("<FocusIn>", lambda e: setattr(self, "_aktiv_diff_panel", self.text1), add="+")
        self.text2.bind("<FocusIn>", lambda e: setattr(self, "_aktiv_diff_panel", self.text2), add="+")
        self.text1.bind("<Button-1>", lambda e: setattr(self, "_aktiv_diff_panel", self.text1), add="+")
        self.text2.bind("<Button-1>", lambda e: setattr(self, "_aktiv_diff_panel", self.text2), add="+")

        for t in (self.text1, self.text2):
            t.tag_configure("elter", background="#ffcccc")
            t.tag_configure("sor_elter", background="#fff3b0")
            t.tag_configure("egyezes", background=SZINEK["egyezes"], foreground=szin_kontraszt(SZINEK["egyezes"]))
            t.tag_configure("hdiff_kijelolt", background=SZINEK["hdiff_kijelolt"],
                             foreground=szin_kontraszt(SZINEK["hdiff_kijelolt"]), underline=True)
            self._frissit_diff_opciok()
            
    def _frissit_diff_opciok(self, event=None):

        aktualis_mod = untr(self.ellenorzes_tipus_var.get())

        if aktualis_mod.startswith("Hagyományos Diff"):
            self.diff_opcio_keret.pack(side="left", padx=6)
            self.hdiff_nav_szeparator.pack(side="left", fill="y", padx=6)
            self.hdiff_nav_keret.pack(side="left")

        else:
            self.diff_opcio_keret.pack_forget()
            self.hdiff_nav_szeparator.pack_forget()
            self.hdiff_nav_keret.pack_forget()

    def _epitsd_mappa_nezet(self, szulo):
        felso_keret = ttk.Frame(szulo, padding=10)
        felso_keret.pack(side="top", fill="x")

        ttk.Button(felso_keret, text=tr("Mappa kiválasztása és kötegelt vizsgálat..."),
                   command=self.mappa_kotegelt_vizsgalat).pack(side="left", padx=5)

        self.mappa_cache_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(felso_keret, text=tr("Gyorsítótár (cache) használata"),
                        variable=self.mappa_cache_var).pack(side="left", padx=10)

        self.mappa_multiproc_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(felso_keret, text=tr("Több CPU-mag (multiprocessing) használata"),
                        variable=self.mappa_multiproc_var).pack(side="left", padx=10)

        ttk.Label(felso_keret, text=tr(" (Tipp: Kattints a fejlécbe a rendezéshez, vagy duplán a sorra a megnyitáshoz!)")).pack(side="left", padx=10)

        tábla_keret = ttk.Frame(szulo, padding=10)
        tábla_keret.pack(side="top", fill="both", expand=True)

        oszlopok = ("fajl1", "fajl2", "winnowing", "tfidf", "simhash")
        self.tree = ttk.Treeview(tábla_keret, columns=oszlopok, show="headings", selectmode="browse")
        
        self.tree.heading("fajl1", text=tr("Első Fájl ▲"), command=lambda: self._sorbaz_mappa("fajl1"))
        self.tree.heading("fajl2", text=tr("Második Fájl"), command=lambda: self._sorbaz_mappa("fajl2"))
        self.tree.heading("winnowing", text=tr("Winnowing Ujjlenyomat (%)"), command=lambda: self._sorbaz_mappa("winnowing"))
        self.tree.heading("tfidf", text=tr("TF-IDF Tartalmi Egyezés (%)"), command=lambda: self._sorbaz_mappa("tfidf"))
        self.tree.heading("simhash", text=tr("Simhash Egyezés (%)"), command=lambda: self._sorbaz_mappa("simhash"))

        self.tree.column("fajl1", width=230, anchor="w")
        self.tree.column("fajl2", width=230, anchor="w")
        self.tree.column("winnowing", width=160, anchor="center")
        self.tree.column("tfidf", width=160, anchor="center")
        self.tree.column("simhash", width=140, anchor="center")

        self.tree.bind("<Double-1>", self._mappa_elem_duplakatt)

        scrollbar = ttk.Scrollbar(tábla_keret, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=scrollbar.set)

        self.tree.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

    def _sorbaz_mappa(self, col):
        data = [(self.tree.set(child, col), child) for child in self.tree.get_children('')]
        if not data:
            return

        reverse = self._tree_sort_state.get(col, False)

        def parse_val(item_tuple):
            val, child = item_tuple
            if col in ("winnowing", "tfidf", "simhash"):
                try:
                    clean = val.replace('%', '').strip().replace(',', '.')
                    return (float(clean), child)
                except ValueError:
                    return (0.0, child)
            else:
                return (val.lower(), child)

        data_parsed = [parse_val(item) for item in data]
        data_parsed.sort(key=lambda x: x[0], reverse=reverse)

        for index, (val, child) in enumerate(data_parsed):
            self.tree.move(child, '', index)

        self._tree_sort_state[col] = not reverse

        alap_nevek = {
            "fajl1": "Első Fájl",
            "fajl2": tr("Második Fájl"),
            "winnowing": tr("Winnowing Ujjlenyomat (%)"),
            "tfidf": tr("TF-IDF Tartalmi Egyezés (%)"),
            "simhash": tr("Simhash Egyezés (%)")
        }

        for c in alap_nevek.keys():
            nyil = ""
            if c == col:
                nyil = " ▼" if reverse else " ▲"
            self.tree.heading(c, text=alap_nevek[c] + nyil)

    def _egyezesi_tagek_torlese(self):
        for t in (self.text1, self.text2):
            for tag in list(t.tag_names()):
                if tag.startswith("egyez_"): t.tag_remove(tag, "1.0", "end")

    def _egyezesi_blokkok_alkalmazasa(self, blokkok):
        self._egyezesi_tagek_torlese()
        paletta=SZINEK["paletta"]
        t1=self.text1.get("1.0","end-1c"); t2=self.text2.get("1.0","end-1c")
        for bl in blokkok:
            tag=f"egyez_{bl['id']}"; szin=paletta[(bl["id"]-1)%len(paletta)]
            for t in (self.text1,self.text2): t.tag_configure(tag,background=szin,foreground=szin_kontraszt(szin),underline=True)
            self.text1.tag_add(tag,_offset_to_tk_index(t1,bl["start1"]),_offset_to_tk_index(t1,bl["end1"]))
            self.text2.tag_add(tag,_offset_to_tk_index(t2,bl["start2"]),_offset_to_tk_index(t2,bl["end2"]))

    def _ugras_egyezesre(self, blokkok, index):
        if not blokkok: return
        index=max(0,min(index,len(blokkok)-1)); bl=blokkok[index]
        t1=self.text1.get("1.0","end-1c"); t2=self.text2.get("1.0","end-1c")
        for t in (self.text1,self.text2):
            t.tag_remove("egyez_kijelolt","1.0","end")
            t.tag_configure("egyez_kijelolt",background=SZINEK["kijelolt_hatter"],foreground=SZINEK["kijelolt_szoveg"],underline=True)
        s1,e1=_offset_to_tk_index(t1,bl["start1"]),_offset_to_tk_index(t1,bl["end1"])
        s2,e2=_offset_to_tk_index(t2,bl["start2"]),_offset_to_tk_index(t2,bl["end2"])
        self.text1.tag_add("egyez_kijelolt",s1,e1); self.text2.tag_add("egyez_kijelolt",s2,e2)
        # A kijelölés mindig a többi egyezés-színezés (és minden más címke) fölött legyen,
        # különben a később létrehozott egyez_N címkék elnyomják a sárga kijelölést.
        for t in (self.text1, self.text2):
            t.tag_raise("egyez_kijelolt")
        self.text1.see(s1); self.text2.see(s2)

    def _egyezesi_panel_megjelenitese(self, blokkok, szoveg1, szoveg2):
        """A vizuális egyezések panelje a főablak 3. oszlopában jelenik meg, nem külön ablakban."""
        fo = getattr(self, "_fo_keret", None)
        if fo is None:
            return None

        if self._egyezesi_panel is not None and self._egyezesi_panel.winfo_exists():
            self._egyezesi_panel.destroy()

        fo.columnconfigure(2, weight=0, minsize=245)
        panel = ttk.LabelFrame(fo, text=tr(" 🔎 Egyezések "), padding=6)
        panel.grid(row=0, column=2, rowspan=2, sticky="nsew", padx=(6, 4), pady=4)
        panel.columnconfigure(0, weight=1)
        panel.rowconfigure(2, weight=1)
        self._egyezesi_panel = panel

        fejlec = ttk.Frame(panel)
        fejlec.grid(row=0, column=0, sticky="ew", pady=(0, 5))
        fejlec.columnconfigure(0, weight=1)
        minimum = self._egyezesi_min_szavak_var.get()
        fejlec_cim = tr(f"{len(blokkok)} pontos egyezési szakasz")
        fejlec_leiras = tr(f"Legalább {minimum} egymást követő azonos szó")
        ttk.Label(
            fejlec,
            text=fejlec_cim,
            font=("TkDefaultFont", 10, "bold"),
            wraplength=225,
        ).grid(row=0, column=0, sticky="w")
        ttk.Label(
            fejlec,
            text=fejlec_leiras,
            foreground="#666666",
            wraplength=225,
        ).grid(row=1, column=0, sticky="w")

        minimum_keret = ttk.Frame(fejlec)
        minimum_keret.grid(row=2, column=0, sticky="w", pady=(5, 0))
        ttk.Label(minimum_keret, text=tr("Min:")).pack(side="left", padx=(0, 5))
        minimum_valaszto = ttk.Spinbox(
            minimum_keret, from_=2, to=10, width=3,
            textvariable=self._egyezesi_min_szavak_var,
            command=self._minimum_egyezes_valtasa
        )
        minimum_valaszto.pack(side="left")
        ttk.Label(minimum_keret, text=tr("szó")).pack(side="left", padx=(4, 0))
        minimum_valaszto.bind("<Return>", self._minimum_egyezes_valtasa)
        minimum_valaszto.bind("<FocusOut>", self._minimum_egyezes_valtasa)

        nav = ttk.Frame(panel)
        nav.grid(row=1, column=0, sticky="ew", pady=(0, 5))
        aktualis = tk.IntVar(value=0)
        lbl_akt = ttk.Label(nav, text="")
        lbl_akt.pack(side="left", padx=(2, 8))

        cols = ("id", "szavak", "bal", "jobb")
        tree = ttk.Treeview(panel, columns=cols, show="headings", selectmode="browse")
        tree.heading("id", text="#")
        tree.heading("szavak", text=tr("Szó"))
        tree.heading("bal", text=tr("Bal"))
        tree.heading("jobb", text=tr("Jobb"))
        tree.column("id", width=32, anchor="center", stretch=False)
        tree.column("szavak", width=68, anchor="center", stretch=False)
        tree.column("bal", width=58, anchor="center", stretch=False)
        tree.column("jobb", width=58, anchor="center", stretch=False)
        tree.grid(row=2, column=0, sticky="nsew")

        sb = ttk.Scrollbar(panel, orient="vertical", command=tree.yview)
        sb.grid(row=2, column=1, sticky="ns")
        tree.configure(yscrollcommand=sb.set)

        reszlet = tk.Text(panel, height=6, width=1, wrap="word", font=("TkDefaultFont", 9),
                          state="disabled", relief="flat", background="#f7f7f7")
        reszlet.grid(row=3, column=0, columnspan=2, sticky="ew", pady=(6, 0))

        for bl in blokkok:
            bal_sor = szoveg1[:bl["start1"]].count("\n") + 1
            jobb_sor = szoveg2[:bl["start2"]].count("\n") + 1
            tree.insert("", "end", iid=str(bl["id"]),
                        values=(bl["id"], bl["words"], bal_sor, jobb_sor))

        def mutat_reszlet(bl):
            resz = re.sub(r"\s+", " ", bl["text1"]).strip()
            if len(resz) > 700:
                resz = resz[:700] + "…"
            reszlet.configure(state="normal")
            reszlet.delete("1.0", "end")
            reszlet.insert("1.0", tr(f"#{bl['id']}  •  {bl['words']} szó") + f"\n\n{resz}")
            reszlet.configure(state="disabled")

        # Fontos: a Treeview <<TreeviewSelect>> eseménye akkor is lefut,
        # amikor programból meghívjuk a selection_set()-et. A korábbi változatban
        # ez visszahívta a kivalaszt()-ot, amely újra selection_set()-et hívott,
        # ezért végtelen eseménylánc alakult ki és a program lefagyott.
        _belső_kijeloles = {"aktiv": False}

        def kivalaszt(index, allit_kijelolest=True):
            if not blokkok:
                return
            index = max(0, min(index, len(blokkok) - 1))
            aktualis.set(index)
            iid = str(blokkok[index]["id"])

            if allit_kijelolest:
                _belső_kijeloles["aktiv"] = True
                try:
                    tree.selection_set(iid)
                    tree.focus(iid)
                    tree.see(iid)
                finally:
                    _belső_kijeloles["aktiv"] = False

            mutat_reszlet(blokkok[index])
            lbl_akt.configure(text=f"{index + 1} / {len(blokkok)}")
            self._ugras_egyezesre(blokkok, index)

        def kivalaszt_esemeny(event=None):
            # A programból indított selection_set() eseményét nem dolgozzuk fel
            # még egyszer. Ez szünteti meg a lefagyást okozó rekurziót.
            if _belső_kijeloles["aktiv"]:
                return
            sel = tree.selection()
            if sel:
                try:
                    index = next(
                        i for i, bl in enumerate(blokkok)
                        if str(bl["id"]) == str(sel[0])
                    )
                    kivalaszt(index, allit_kijelolest=False)
                except (ValueError, TypeError, StopIteration):
                    pass

        def eloz(delta):
            if blokkok:
                kivalaszt((aktualis.get() + delta) % len(blokkok))

        ttk.Button(nav, text="◀", width=3, command=lambda: eloz(-1)).pack(side="left", padx=2)
        ttk.Button(nav, text="▶", width=3, command=lambda: eloz(1)).pack(side="left", padx=2)
        ttk.Button(nav, text=tr("✕ Bezár"), command=self._egyezesi_panel_bezarasa).pack(side="right")

        tree.bind("<<TreeviewSelect>>", kivalaszt_esemeny)
        tree.bind("<Double-1>", kivalaszt_esemeny)

        if blokkok:
            kivalaszt(0)
        else:
            lbl_akt.configure(text=tr("Nincs egyezés"))

        return panel

    def _egyezesi_panel_bezarasa(self):
        panel = getattr(self, "_egyezesi_panel", None)
        if panel is not None and panel.winfo_exists():
            panel.destroy()
        self._egyezesi_panel = None
        if hasattr(self, "_fo_keret"):
            self._fo_keret.columnconfigure(2, weight=0, minsize=0)

    def vizualis_egyezesek(self):
        szoveg1 = self.text1.get("1.0", "end-1c")
        szoveg2 = self.text2.get("1.0", "end-1c")
        if not szoveg1.strip() or not szoveg2.strip():
            messagebox.showwarning(tr("Egyezések"), tr("Mindkét szövegmezőnek tartalmaznia kell szöveget."))
            return

        self._egyezesi_szovegek = (szoveg1, szoveg2)
        self._egyezesi_min_szavak_var = tk.IntVar(value=5)
        blokkok = _vizualis_egyezesi_blokkok(szoveg1, szoveg2, 5)
        self._egyezesi_blokkok_alkalmazasa(blokkok)
        self._egyezesi_panel_megjelenitese(blokkok, szoveg1, szoveg2)
        self._utolso_egyezesi_blokkok = blokkok
        self.statusz_var.set(
            tr(f"Vizuális egyezésvizsgálat: {len(blokkok)} pontos szakasz kiemelve a két szövegben.")
        )

    def teljes_kepernyo_ekg(self):
        """Teljes képernyős kétpaneles nézet EKG-szerű egyezési hullámmal."""
        szoveg1 = self.text1.get("1.0", "end-1c")
        szoveg2 = self.text2.get("1.0", "end-1c")
        if not szoveg1.strip() or not szoveg2.strip():
            messagebox.showwarning(tr("Egyezések"), tr("Mindkét szövegmezőnek tartalmaznia kell szöveget."))
            return
        self._mozgasjelzo_inditasa(tr("Egyezési hullám számítása…"))
        eredmeny = {}

        def munka():
            try:
                eredmeny["adat"] = ekg_adatok_szamitasa(szoveg1, szoveg2)
            except Exception as e:
                eredmeny["hiba"] = e

        szal = threading.Thread(target=munka, daemon=True)
        szal.start()

        def varakozas():
            if szal.is_alive():
                self.after(80, varakozas)
                return
            self._mozgasjelzo_leallitasa()
            if "hiba" in eredmeny:
                messagebox.showerror(tr("Hiba"), str(eredmeny["hiba"]))
                return
            adat = eredmeny["adat"]
            if not adat["szavak"][0] or not adat["szavak"][1]:
                messagebox.showwarning(tr("Egyezések"), tr("Mindkét szövegmezőnek tartalmaznia kell szöveget."))
                return
            EgyezesEKGNezet(self, szoveg1, szoveg2, self.cimke1_var.get(), self.cimke2_var.get(), adat)

        self.after(80, varakozas)

    def _minimum_egyezes_valtasa(self, event=None):
        """A 2–10 szavas küszöb módosításakor frissíti a kiemeléseket. A
        léptetőgomb (Spinbox) egyetlen tartott kattintásra vagy gyors
        pörgetésre is sok eseményt küldhet egymás után; ha mindegyikre
        azonnal újraszámolnánk a teljes egyezéskeresést és újraépítenénk a
        panelt (ami nagyobb szövegnél nem elhanyagolható munka), az
        használat közben "megakadva" tenné a programot. Ezért a tényleges,
        költséges újraszámolást egy rövid (300 ms) késleltetéssel, csak az
        eseménysorozat VÉGÉN indítjuk el."""
        try:
            minimum = max(2, min(10, int(self._egyezesi_min_szavak_var.get())))
        except (ValueError, tk.TclError):
            minimum = 5
        self._egyezesi_min_szavak_var.set(minimum)

        elozo_id = getattr(self, "_min_egyezes_debounce_id", None)
        if elozo_id is not None:
            try:
                self.after_cancel(elozo_id)
            except (ValueError, tk.TclError):
                pass
        self._min_egyezes_debounce_id = self.after(
            300, lambda: self._minimum_egyezes_ujraszamolasa(minimum)
        )

    def _minimum_egyezes_ujraszamolasa(self, minimum):
        self._min_egyezes_debounce_id = None
        szovegek = getattr(self, "_egyezesi_szovegek", None)
        if not szovegek:
            return
        blokkok = _vizualis_egyezesi_blokkok(*szovegek, minimum)
        self._egyezesi_blokkok_alkalmazasa(blokkok)
        self._egyezesi_panel_megjelenitese(blokkok, *szovegek)
        self._utolso_egyezesi_blokkok = blokkok
        self.statusz_var.set(tr(f"Pontos egyezés ({minimum} szó): {len(blokkok)} szakasz a két szövegben."))

    def _frissit_sorszamok(self, widget):
        """A Text mező bal oldalán megjeleníti a tényleges (logikai) sorszámokat.

        Gyors változat: a látható képernyősorokat y-koordináta alapján járja végig
        (a Tk ezeket már kiszámolta), így nem kell a „+ 1 display line” indexszámítás,
        ami nagyon hosszú, tördeletlen soroknál a sor elejétől újra kiszámolná az egészet."""
        canvas = getattr(widget, "line_numbers_canvas", None)
        if canvas is None or not canvas.winfo_exists():
            return
        canvas.delete("all")
        try:
            magassag = widget.winfo_height()
            x = canvas.winfo_width() - 6
            y = 0
            utolso_y = None
            for _ in range(400):
                if y >= magassag:
                    break
                idx = widget.index(f"@0,{y}")
                bbox = widget.dlineinfo(idx)
                if bbox is None or bbox[1] == utolso_y or bbox[1] + bbox[3] <= y:
                    break
                utolso_y = bbox[1]
                canvas.create_text(x, bbox[1], anchor="ne", text=idx.split(".")[0],
                                   font=("Consolas", 10), fill="#666666")
                y = bbox[1] + max(1, bbox[3])
        except tk.TclError:
            pass

    def _sorszam_kesleltet(self, widget):
        """A sorszámsáv frissítését egy eseményciklusonként legfeljebb egyszer futtatja
        (gyors görgetésnél nem torlódnak fel a újrarajzolások)."""
        attr = f"_sorszam_fuggo_{id(widget)}"
        if getattr(self, attr, False):
            return
        setattr(self, attr, True)

        def futtat():
            setattr(self, attr, False)
            self._frissit_sorszamok(widget)
        self.after_idle(futtat)

    def _frissit_sorszamok_debounce(self, widget, keses_ms=60):
        """Egy <Configure> esemény (pl. ablak átméretezése vagy maximalizálása)
        rövid idő alatt akár tucatszor is lefuthat, mert a szövegdoboz ÉS a
        mellette lévő sorszám-canvas is saját <Configure> eseményt kap minden
        egyes méretváltozásnál. Ha mindegyikre azonnal, szinkron módon
        újraszámolnánk és újrarajzolnánk a teljes sorszám-sávot, az
        átméretezés közben szaggatottá, "lefagyva-mintha" tenné a felületet.
        Ehelyett csak az eseménysorozat VÉGÉN, egyszer rajzolunk újra: minden
        új hívás törli az előzőleg beütemezett rajzolást, és újraindítja a
        rövid késleltetést."""
        attr = f"_sorszam_debounce_id_{id(widget)}"
        elozo_id = getattr(self, attr, None)
        if elozo_id is not None:
            try:
                self.after_cancel(elozo_id)
            except (ValueError, tk.TclError):
                pass
        uj_id = self.after(keses_ms, lambda: self._frissit_sorszamok(widget))
        setattr(self, attr, uj_id)

    def _keszits_szoveg_dobozt(self, szulo, oszlop):
        keret = ttk.Frame(szulo)
        keret.grid(row=1, column=oszlop, sticky="nsew", padx=(2, 2), pady=4)
        keret.rowconfigure(0, weight=1)
        keret.columnconfigure(1, weight=1)

        # Keskeny, beépített sorszám-gutter. A fő Text működése változatlan marad.
        sorszam_canvas = tk.Canvas(keret, width=34, background="#f4f4f4",
                                   highlightthickness=0, bd=0)
        sorszam_canvas.grid(row=0, column=0, sticky="ns")

        szovegdoboz = tk.Text(keret, wrap="word", undo=True, font=self.szoveg_font)
        szovegdoboz.grid(row=0, column=1, sticky="nsew")
        # Láthatatlan jelölő tag: ezzel jelöljük meg azokat a sortöréseket,
        # amiket MI szúrtunk be csak a megjelenítés kedvéért (lásd
        # _hosszu_sorok_tordelese_jelolt / fajl_megnyitas / fajl_mentes) - a
        # fájl tartalma emiatt sosem változik meg ténylegesen, mentéskor
        # ezeket visszaalakítjuk szóközzé.
        szovegdoboz.tag_configure("mu_tores")

        vsb = ttk.Scrollbar(keret, orient="vertical", command=szovegdoboz.yview)
        vsb.grid(row=0, column=2, sticky="ns")
        hsb = ttk.Scrollbar(keret, orient="horizontal", command=szovegdoboz.xview)
        hsb.grid(row=1, column=1, sticky="ew")

        def yscroll(*args):
            vsb.set(*args)
            self._sorszam_kesleltet(szovegdoboz)

        szovegdoboz.configure(yscrollcommand=yscroll, xscrollcommand=hsb.set)
        szovegdoboz.vbar = vsb
        szovegdoboz.line_numbers_canvas = sorszam_canvas

        szovegdoboz.bind("<KeyRelease>", lambda e: self._sorszam_kesleltet(szovegdoboz), add="+")
        def modified_sorszam(event=None):
            self._sorszam_kesleltet(szovegdoboz)
            try:
                szovegdoboz.edit_modified(False)
            except tk.TclError:
                pass
        szovegdoboz.bind("<<Modified>>", modified_sorszam, add="+")
        szovegdoboz.bind("<Configure>", lambda e: self._frissit_sorszamok_debounce(szovegdoboz), add="+")
        sorszam_canvas.bind("<Configure>", lambda e: self._frissit_sorszamok_debounce(szovegdoboz))

        self._adj_context_menu(szovegdoboz)
        self.after_idle(lambda: self._frissit_sorszamok(szovegdoboz))
        return szovegdoboz

    def _adj_context_menu(self, widget):
        menu = tk.Menu(widget, tearoff=0)
        menu.add_command(label=tr("Kivágás"), command=lambda: widget.event_generate("<<Cut>>"))
        menu.add_command(label=tr("Másolás"), command=lambda: widget.event_generate("<<Copy>>"))
        menu.add_command(label=tr("Beillesztés"), command=lambda: widget.event_generate("<<Paste>>"))
        menu.add_separator()
        menu.add_command(label=tr("Mindent kijelöl"), command=lambda: widget.tag_add("sel", "1.0", "end"))

        def megjelenit(event):
            menu.tk_popup(event.x_root, event.y_root)

        widget.bind("<Button-3>", megjelenit)
        widget.bind("<Button-2>", megjelenit)

    def _szinkron_yview_factory(self, forras, cel):
        def kezelo(*args):
            forras.yview(*args)
            if self.szinkron_var.get():
                cel.yview(*args)
        return kezelo

    @staticmethod
    def _hosszu_sorok_tordelese_jelolt(szoveg, max_hossz=2000):
        """Egy nagyon hosszú, sortörés nélküli logikai sor (jellemzően egy
        több oldalas, de folyószövegként - nem soronként - mentett .txt fájl)
        a Tk 'wrap=word' tördelő motorját mérhetően lelassítja (több száz
        ezer karakternél már másodperces késést okoz). Ez a függvény a
        max_hossz-at meghaladó sorokat a bennük lévő whitespace-futamok
        (szóközök) mentén MEGJELENÍTÉSI célból újabb sortörésekkel tagolja,
        és visszaadja a beszúrt sortörés-karakterek pozícióját is (a végleges,
        tördelt szövegen belüli karakter-offset). Fontos: egyetlen eredeti
        karaktert sem távolít el vagy cserél le - csak új sortörést told be a
        meglévő szóköz-futamok végére -, ezért a fajl_mentes ezeket pusztán
        TÖRÖLVE (nem szóközre cserélve) bit-pontosan vissza tudja állítani az
        eredeti tartalmat, a szóközök/whitespace-ek eredeti számától
        függetlenül. Ha egy "szó" önmagában is túl hosszú (nincs benne
        whitespace), szükség esetén kényszerből, a szó közepén is betold egy
        jelölt sortörést. A már soronként tagolt fájlokat (pl. .srt)
        gyakorlatilag nem érinti."""
        resz = []
        pozok = []
        hossz = 0
        sorok = szoveg.split("\n")
        for sor_idx, sor in enumerate(sorok):
            if sor_idx > 0:
                resz.append("\n")
                hossz += 1
            if len(sor) <= max_hossz:
                resz.append(sor)
                hossz += len(sor)
                continue
            darabok = [d for d in re.split(r'(\s+)', sor) if d]
            aktualis_hossz = 0
            for d in darabok:
                if d.strip() == "":
                    resz.append(d)
                    hossz += len(d)
                    aktualis_hossz += len(d)
                    if aktualis_hossz > max_hossz:
                        pozok.append(hossz)
                        resz.append("\n")
                        hossz += 1
                        aktualis_hossz = 0
                else:
                    while aktualis_hossz + len(d) > max_hossz and len(d) > 1:
                        hely = max(1, max_hossz - aktualis_hossz)
                        resz.append(d[:hely])
                        hossz += hely
                        pozok.append(hossz)
                        resz.append("\n")
                        hossz += 1
                        d = d[hely:]
                        aktualis_hossz = 0
                    resz.append(d)
                    hossz += len(d)
                    aktualis_hossz += len(d)
        return "".join(resz), pozok

    def fajl_megnyitas(self, melyik):
        utvonal = filedialog.askopenfilename(
            title=tr("Szöveg / Felirat fájl megnyitása"),
            filetypes=[("Támogatott szöveg- és dokumentumfájlok",
                        " ".join("*" + e for e in TAMOGATOTT_KITERJESZTESEK)), ("Minden fájl", "*.*")]
        )
        if not utvonal:
            return
        try:
            tartalom = olvas_szoveg_fajl(utvonal)
        except Exception as e:
            messagebox.showerror(tr("Hiba"), tr(f"Nem sikerült megnyitni a fájlt:\n{e}"))
            return

        self._allapot_mentes()
        megjelenitett, mu_pozok = self._hosszu_sorok_tordelese_jelolt(tartalom)
        if melyik == 1:
            self.fajl1_utvonal = utvonal
            self.text1.delete("1.0", "end")
            self.text1.insert("1.0", megjelenitett)
            for pos in mu_pozok:
                idx = _offset_to_tk_index(megjelenitett, pos)
                self.text1.tag_add("mu_tores", idx, f"{idx}+1c")
            self.after_idle(lambda: self._frissit_sorszamok(self.text1))
            self.cimke1_var.set(tr(f"Bal fájl: {Path(utvonal).name}"))
        else:
            self.fajl2_utvonal = utvonal
            self.text2.delete("1.0", "end")
            self.text2.insert("1.0", megjelenitett)
            for pos in mu_pozok:
                idx = _offset_to_tk_index(megjelenitett, pos)
                self.text2.tag_add("mu_tores", idx, f"{idx}+1c")
            self.after_idle(lambda: self._frissit_sorszamok(self.text2))
            self.cimke2_var.set(tr(f"Jobb fájl: {Path(utvonal).name}"))

    _MENTESI_FORMATUMOK = [
        (".txt", "Szövegfájl (kiemelés nélkül)", "*.txt"),
        (".docx", "Word dokumentum (kiemelésekkel)", "*.docx"),
        (".odt", "OpenDocument szöveg (kiemelésekkel)", "*.odt"),
        (".html", "HTML oldal (kiemelésekkel)", "*.html"),
    ]
    _MENTESI_TARTALMAK = [
        ("teljes", "A teljes szöveg, ahogy látom (kijelölésekkel, színekkel)"),
        ("egyezes", "Csak az egyezések"),
        ("elteres", "Csak az eltérések"),
    ]

    def _mentesi_tartalom_ablak(self):
        """Azt választja ki előre a felhasználó, hogy a teljes szöveget, csak az egyezéseket,
        vagy csak az eltéréseket akarja-e menteni. Alapértelmezés: a teljes szöveg (mint eddig)."""
        win = tk.Toplevel(self)
        win.title(tr("Mentés másként"))
        win.resizable(False, False)
        win.transient(self)
        eredmeny = {"mod": None}
        valasztott = tk.StringVar(value="teljes")

        keret = ttk.Frame(win, padding=14)
        keret.pack(fill="both", expand=True)
        ttk.Label(keret, text=tr("Mit mentsek?"),
                 font=("Segoe UI", 10, "bold")).pack(anchor="w", pady=(0, 8))
        for kulcs, cim in self._MENTESI_TARTALMAK:
            ttk.Radiobutton(keret, text=tr(cim), value=kulcs, variable=valasztott).pack(anchor="w", pady=3)

        try:
            minimum = max(2, min(10, int(getattr(self, "_egyezesi_min_szavak_var", tk.IntVar(value=5)).get())))
        except (ValueError, tk.TclError):
            minimum = 5

        ttk.Label(
            keret,
            text=tr("Az egyezések és eltérések mentése a Visual Match View alapján történik: legalább {minimum} egymást követő azonos szó.").format(minimum=minimum),
            foreground="#666666",
            wraplength=430,
            justify="left",
        ).pack(anchor="w", pady=(8, 0))

        def ok(event=None):
            eredmeny["mod"] = valasztott.get()
            win.destroy()

        gombok = ttk.Frame(keret)
        gombok.pack(fill="x", pady=(14, 0))
        ttk.Button(gombok, text=tr("Mégse"), command=win.destroy).pack(side="right")
        ttk.Button(gombok, text=tr("Tovább"), command=ok).pack(side="right", padx=(0, 6))
        win.bind("<Return>", ok)
        win.bind("<Escape>", lambda e: win.destroy())
        win.update_idletasks()
        x = self.winfo_rootx() + (self.winfo_width() - win.winfo_width()) // 2
        y = self.winfo_rooty() + (self.winfo_height() - win.winfo_height()) // 2
        win.geometry(f"+{max(0, x)}+{max(0, y)}")
        win.grab_set()
        win.focus_force()
        win.wait_window()
        return eredmeny["mod"]

    def _mentesi_format_ablak(self, javasolt_ext):
        """Előbb a formátumot választja ki a felhasználó (rádiógombokkal), utána jön csak a
        fájlnév ablak - így a rendszer mindig magától illeszti a helyes kiterjesztést, nem kell
        kézzel beírni, és a Word/OpenDocument/HTML/sima szöveg egyértelműen külön választható."""
        win = tk.Toplevel(self)
        win.title(tr("Mentés másként"))
        win.resizable(False, False)
        win.transient(self)
        eredmeny = {"ext": None}
        valasztott = tk.StringVar(value=javasolt_ext if javasolt_ext in dict(
            (e, None) for e, _, _ in self._MENTESI_FORMATUMOK) else ".txt")

        keret = ttk.Frame(win, padding=14)
        keret.pack(fill="both", expand=True)
        ttk.Label(keret, text=tr("Milyen formátumban mentsem?"),
                 font=("Segoe UI", 10, "bold")).pack(anchor="w", pady=(0, 8))
        for ext, cim, _ in self._MENTESI_FORMATUMOK:
            ttk.Radiobutton(keret, text=f"{tr(cim)}  ({ext})", value=ext,
                           variable=valasztott).pack(anchor="w", pady=3)

        def ok(event=None):
            eredmeny["ext"] = valasztott.get()
            win.destroy()

        gombok = ttk.Frame(keret)
        gombok.pack(fill="x", pady=(14, 0))
        ttk.Button(gombok, text=tr("Mégse"), command=win.destroy).pack(side="right")
        ttk.Button(gombok, text=tr("Tovább"), command=ok).pack(side="right", padx=(0, 6))
        win.bind("<Return>", ok)
        win.bind("<Escape>", lambda e: win.destroy())
        win.update_idletasks()
        x = self.winfo_rootx() + (self.winfo_width() - win.winfo_width()) // 2
        y = self.winfo_rooty() + (self.winfo_height() - win.winfo_height()) // 2
        win.geometry(f"+{max(0, x)}+{max(0, y)}")
        win.grab_set()
        win.focus_force()
        win.wait_window()
        return eredmeny["ext"]

    def _vizualis_mentesi_blokkok(self, szoveg1, szoveg2):
        """A mentéshez pontosan ugyanazt a Visual Match View egyezéslistát adja,
        amelyet a felhasználó a 2–10 szavas beállítással lát.

        Ha a Visual Match View már futott és a szövegek nem változtak, a már
        kiszámított blokklistát használjuk. Ha a szöveg azóta megváltozott,
        ugyanazzal a jelenlegi küszöbbel újraszámoljuk.
        """
        try:
            minimum = max(2, min(10, int(self._egyezesi_min_szavak_var.get())))
        except (AttributeError, ValueError, tk.TclError):
            minimum = 5

        elozo_szovegek = getattr(self, "_egyezesi_szovegek", None)
        elozo_blokkok = getattr(self, "_utolso_egyezesi_blokkok", None)
        if elozo_szovegek == (szoveg1, szoveg2) and elozo_blokkok is not None:
            return elozo_blokkok, minimum

        blokkok = _vizualis_egyezesi_blokkok(szoveg1, szoveg2, minimum)
        return blokkok, minimum

    def fajl_mentes(self, melyik):
        widget = self.text1 if melyik == 1 else self.text2
        alap_utvonal = self.fajl1_utvonal if melyik == 1 else self.fajl2_utvonal

        tartalom_mod = self._mentesi_tartalom_ablak()
        if not tartalom_mod:
            return

        javasolt_ext = ".txt"
        alap_nev = "szoveg"
        if alap_utvonal:
            eredeti_nev = Path(alap_utvonal)
            alap_nev = eredeti_nev.stem
            # a sima szöveges kiterjesztéseket (.md, .srt, stb.) is a "Szövegfájl" választás jelenti,
            # a formázott mentéshez (Word/OpenDocument/HTML) csak azok a kiterjesztések ajánlódnak fel
            if eredeti_nev.suffix.lower() in FORMAZOTT_MENTES_KITERJESZTESEK:
                javasolt_ext = eredeti_nev.suffix.lower()

        ext = self._mentesi_format_ablak(javasolt_ext)
        if not ext:
            return
        cim = next(c for e, c, _ in self._MENTESI_FORMATUMOK if e == ext)
        minta = next(m for e, _, m in self._MENTESI_FORMATUMOK if e == ext)

        utolso_resz = {"teljes": "szerkesztett", "egyezes": "egyezesek", "elteres": "elteresek"}[tartalom_mod]
        utvonal = filedialog.asksaveasfilename(
            title=tr("Mentés másként"),
            initialfile=f"{alap_nev}_{utolso_resz}{ext}",
            defaultextension=ext,
            confirmoverwrite=True,
            filetypes=[(tr(cim), minta), (tr("Minden fájl"), "*.*")]
        )
        if not utvonal:
            return
        if Path(utvonal).suffix == "":
            utvonal += ext                       # ha a rendszer mégsem illesztette (pl. Linux/Mac)
        ext = Path(utvonal).suffix.lower()
        # Az eredeti fájl felülírását nem engedjük: mindig új néven kell menteni.
        try:
            if alap_utvonal and os.path.exists(utvonal) and os.path.samefile(utvonal, alap_utvonal):
                messagebox.showwarning(tr("Figyelem"), tr("Az eredeti fájl nem írható felül. Kérlek, adj meg másik fájlnevet!"))
                return
        except OSError:
            pass
        try:
            if tartalom_mod == "teljes":
                if ext in FORMAZOTT_MENTES_KITERJESZTESEK:
                    futasok = widget_futasok(widget, "teljes")
                    mentes_formazott(utvonal, futasok, Path(utvonal).stem)
                else:
                    with open(utvonal, "w", encoding="utf-8") as f:
                        f.write(self._eredeti_tartalom_visszaallitasa(widget))
            else:
                # A szűrt mentés NEM a hagyományos Diff tagekből dolgozik.
                # A Visual Match View aktuális, 2–10 szavas blokkjai az igazságforrás.
                szoveg1 = self.text1.get("1.0", "end-1c")
                szoveg2 = self.text2.get("1.0", "end-1c")
                blokkok, minimum = self._vizualis_mentesi_blokkok(szoveg1, szoveg2)
                oldal = 1 if melyik == 1 else 2
                futasok = vizualis_widget_futasok(widget, blokkok, oldal, tartalom_mod)

                if not futasok or not "".join(t for t, _ in futasok).strip():
                    messagebox.showwarning(
                        tr("Figyelem"),
                        tr("Nincs menthető tartalom a választott szűrővel.")
                    )
                    return

                if ext in FORMAZOTT_MENTES_KITERJESZTESEK:
                    mentes_formazott(utvonal, futasok, Path(utvonal).stem)
                else:
                    with open(utvonal, "w", encoding="utf-8") as f:
                        f.write("".join(t for t, _ in futasok))
            messagebox.showinfo(tr("Mentve"), tr(f"Sikeresen elmentve:\n{utvonal}"))
        except Exception as e:
            messagebox.showerror(tr("Hiba"), tr(f"Nem sikerült menteni:\n{e}"))

    @staticmethod
    def _eredeti_tartalom_visszaallitasa(widget):
        """A widget aktuális tartalmát adja vissza, de a fajl_megnyitas által
        csak megjelenítési célból beszúrt sortöréseket ("mu_tores" tag)
        eltávolítja - mivel ezek a fajl_megnyitas oldalán sosem cseréltek le
        vagy távolítottak el eredeti karaktert, csak új sortörést toldottak a
        meglévő whitespace-futamok végére, a puszta TÖRLÉSÜK bit-pontosan
        visszaadja az eredeti tartalmat (a whitespace-ek eredeti számától és
        fajtájától függetlenül), plusz a felhasználó saját, valódi
        szerkesztéseit."""
        tartalom = widget.get("1.0", "end-1c")
        tar_range = widget.tag_ranges("mu_tores")
        if not tar_range:
            return tartalom
        pozok = sorted(
            {int(widget.count("1.0", kezdo, "chars")[0]) for kezdo in tar_range[0::2]},
            reverse=True,
        )
        karakterek = list(tartalom)
        for pos in pozok:
            if 0 <= pos < len(karakterek) and karakterek[pos] == "\n":
                del karakterek[pos]
        return "".join(karakterek)

    def idobelyeg_torles(self, melyik):
        widget = self.text1 if melyik == 1 else self.text2
        eredeti = widget.get("1.0", "end-1c")

        self._allapot_mentes()
        eredeti = eredeti.lstrip("\ufeff")
        uj = IDOBELYEG_SOR.sub("", eredeti)
        uj = IDOBELYEG_INLINE.sub("", uj)
        uj = SORSZAM_SOR.sub("", uj)
        uj = WEBVTT_FEJLEC.sub("", uj)
        sorok = [sor for sor in uj.splitlines() if sor.strip() != ""]
        uj = "\n".join(sorok)

        if uj == eredeti:
            self.statusz_var.set(tr("Nem találtam időbélyeget ebben a szövegben."))
            return

        widget.delete("1.0", "end")
        widget.insert("1.0", uj)
        self.statusz_var.set(tr("Az időbélyegeket eltávolítottam."))

    def sorok_szinkronizalasa(self):
        szoveg1 = self.text1.get("1.0", "end-1c")
        szoveg2 = self.text2.get("1.0", "end-1c")

        sorok1 = szoveg1.split("\n")
        sorok2 = szoveg2.split("\n")

        sm = difflib.SequenceMatcher(None, sorok1, sorok2, autojunk=False)
        uj_sorok1, uj_sorok2, elteres_sorindexek = [], [], []

        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == "equal":
                uj_sorok1.extend(sorok1[i1:i2])
                uj_sorok2.extend(sorok2[j1:j2])
            else:
                b1 = sorok1[i1:i2]
                b2 = sorok2[j1:j2]
                maxh = max(len(b1), len(b2))
                b1 += [""] * (maxh - len(b1))
                b2 += [""] * (maxh - len(b2))

                kezdo_index = len(uj_sorok1)
                elteres_sorindexek.extend(range(kezdo_index, kezdo_index + maxh))
                uj_sorok1.extend(b1)
                uj_sorok2.extend(b2)

        if not uj_sorok1 and not uj_sorok2:
            self.statusz_var.set(tr("Nincs mit szinkronizálni - mindkét fájl üres."))
            return

        self._allapot_mentes()
        for t in (self.text1, self.text2):
            t.tag_remove("elter", "1.0", "end")
            t.tag_remove("sor_elter", "1.0", "end")
            t.tag_remove("egyezes", "1.0", "end")

        self.text1.delete("1.0", "end")
        self.text2.delete("1.0", "end")
        self.text1.insert("1.0", "\n".join(uj_sorok1))
        self.text2.insert("1.0", "\n".join(uj_sorok2))

        for idx in elteres_sorindexek:
            sorszam = idx + 1
            self.text1.tag_add("sor_elter", f"{sorszam}.0", f"{sorszam}.end")
            self.text2.tag_add("sor_elter", f"{sorszam}.0", f"{sorszam}.end")

        self.statusz_var.set(tr(f"Sorok szinkronizálva. Eltérő sorok száma: {len(elteres_sorindexek)}."))

    @staticmethod
    def _szoveg_tisztitas(szoveg, szokoz_ki, irasjel_ki):
        if szokoz_ki:
            szoveg = re.sub(r'\s+', '', szoveg)
        if irasjel_ki:
            szoveg = "".join(ch for ch in szoveg if ch not in IRASJELEK)
        return szoveg

    @staticmethod
    def _szoveg_tisztitas_terkeppel(szoveg, szokoz_ki, irasjel_ki):
        """Ugyanaz, mint a _szoveg_tisztitas, de emellett visszaad egy
        indextérképet is: a megtisztított szöveg minden megmaradt karakteréhez
        megadja, hogy az eredeti (teljes) szövegben hányadik pozíción állt.
        Ez teszi lehetővé, hogy a megtisztított szövegen futtatott diff-egyezéseket
        pontosan vissza lehessen vetíteni az eredeti, teljes szövegre (a Text
        widgetben megjelenő, kattintható kiemeléshez)."""
        kimenet = []
        terkep = []
        for i, ch in enumerate(szoveg):
            if szokoz_ki and ch.isspace():
                continue
            if irasjel_ki and ch in IRASJELEK:
                continue
            kimenet.append(ch)
            terkep.append(i)
        return "".join(kimenet), terkep

    @staticmethod
    def _get_ngrams(text, n=4):
        words = re.findall(r'\w+', text.lower())
        return set(tuple(words[i:i+n]) for i in range(len(words)-n+1))

    @staticmethod
    def _tfidf_cosine_similarity(text1, text2):
        # Ugyanaz a modul szintű függvény, mint a HTML riportban és a mappa-mátrixban.
        return tfidf_cosine_hasonlosag(text1, text2)

    @staticmethod
    def _winnowing_similarity(text1, text2, k=4, w=4):
        # Ugyanaz a modul szintű, stabil hash-t használó függvény, mint a HTML
        # riportban és a mappa-mátrixban (a beépített hash() futásonként változik!).
        return winnowing_hasonlosag(text1, text2, k, w)

    @staticmethod
    def _cosine_similarity(text1, text2):
        _sw = stopszavak_a_szovegekhez(text1, text2)
        words1 = [w for w in re.findall(r'\w+', text1.lower()) if w not in _sw and len(w) > 1]
        words2 = [w for w in re.findall(r'\w+', text2.lower()) if w not in _sw and len(w) > 1]
        
        if not words1 or not words2:
            return 0.0

        v1 = Counter(words1)
        v2 = Counter(words2)
        
        intersection = set(v1.keys()) & set(v2.keys())
        numerator = sum(v1[x] * v2[x] for x in intersection)
        
        sum1 = sum(v**2 for v in v1.values())
        sum2 = sum(v**2 for v in v2.values())
        
        denominator = math.sqrt(sum1) * math.sqrt(sum2)
        if not denominator:
            return 0.0
            
        return float(numerator) / denominator * 100

    @staticmethod
    def _jaccard_similarity(text1, text2):
        s1 = set(re.findall(r'\w+', text1.lower()))
        s2 = set(re.findall(r'\w+', text2.lower()))
        if not s1 and not s2:
            return 100.0
        intersection = s1.intersection(s2)
        union = s1.union(s2)
        return (len(intersection) / len(union)) * 100 if union else 0.0

    @staticmethod
    def _stilisztikai_elemzes(text1, text2):
        def analyze(text):
            words = re.findall(r'\w+', text.lower())
            total_words = len(words)
            unique_words = len(set(words))
            ttr = (unique_words / total_words * 100) if total_words > 0 else 0.0
            avg_word_len = sum(len(w) for w in words) / total_words if total_words > 0 else 0.0
            sentences = [s for s in re.split(r'[.!?]+', text) if s.strip()]
            avg_sent_len = total_words / len(sentences) if sentences else 0.0
            return total_words, unique_words, ttr, avg_word_len, avg_sent_len

        return analyze(text1), analyze(text2)

    @staticmethod
    def _ritmus_elemzes(text1, text2):
        def get_sentence_lengths(text):
            sentences = [s.strip() for s in re.split(r'[.!?]+', text) if s.strip()]
            lengths = [len(re.findall(r'\w+', s)) for s in sentences]
            return lengths

        l1 = get_sentence_lengths(text1)
        l2 = get_sentence_lengths(text2)

        if not l1 or not l2:
            return 0.0, l1, l2

        min_len = min(len(l1), len(l2))
        max_len = max(len(l1), len(l2))
        
        elteresek = sum(abs(l1[i] - l2[i]) for i in range(min_len))
        osszeg_max = sum(max(l1[i], l2[i]) for i in range(min_len)) if min_len > 0 else 1
        
        alap_egyezes = max(0.0, (1.0 - (elteresek / max(1, osszeg_max))) * 100)
        hossz_buntetes = (min_len / max_len) * 100
        
        ritmus_index = (alap_egyezes * 0.7) + (hossz_buntetes * 0.3)
        return ritmus_index, l1, l2

    @staticmethod
    def _rajzolj_osszehasonlito_savakat(canvas, adatok, bal_nev=None, jobb_nev=None):
        """Két értéksor összehasonlító, függőségmentes oszlopdiagramja."""
        if bal_nev is None:
            bal_nev = tr("Bal fájl")
        if jobb_nev is None:
            jobb_nev = tr("Jobb fájl")
        canvas.delete("all")
        canvas.update_idletasks()
        szel, mag = max(canvas.winfo_width(), 500), max(canvas.winfo_height(), 300)
        if not adatok:
            canvas.create_text(szel / 2, mag / 2, text=tr("Nincs megjeleníthető adat."), fill="#666")
            return
        bal = 65
        jobb = 25
        felso = 45
        also = 65
        diagram_mag = max(1, mag - felso - also)
        maximum = max(max(a[1], a[2]) for a in adatok)
        maximum = max(1, maximum)
        canvas.create_rectangle(bal, felso, szel - jobb, mag - also, outline="#b0b0b0")
        for i in range(5):
            y = felso + diagram_mag * i / 4
            ertek = maximum * (1 - i / 4)
            canvas.create_line(bal, y, szel - jobb, y, fill="#e5e5e5")
            canvas.create_text(bal - 7, y, text=f"{ertek:.0f}", anchor="e", fill="#555")
        csoport = (szel - bal - jobb) / len(adatok)
        oszlop = min(36, csoport * 0.28)
        for i, (cimke, bal_ertek, jobb_ertek) in enumerate(adatok):
            kozep = bal + csoport * (i + .5)
            for x, ertek, szin in ((kozep - oszlop - 2, bal_ertek, "#3976b9"),
                                   (kozep + 2, jobb_ertek, "#e4873a")):
                y = mag - also - (ertek / maximum * diagram_mag)
                canvas.create_rectangle(x, y, x + oszlop, mag - also, fill=szin, outline="")
                canvas.create_text(x + oszlop / 2, y - 8, text=f"{ertek:.1f}", font=("TkDefaultFont", 8))
            canvas.create_text(kozep, mag - also + 12, text=cimke, anchor="n", width=max(60, int(csoport - 6)))
        canvas.create_rectangle(bal, 12, bal + 14, 26, fill="#3976b9", outline="")
        canvas.create_text(bal + 20, 19, text=bal_nev, anchor="w")
        canvas.create_rectangle(bal + 145, 12, bal + 159, 26, fill="#e4873a", outline="")
        canvas.create_text(bal + 165, 19, text=jobb_nev, anchor="w")

    @staticmethod
    def _rajzolj_vonaldiagramot(canvas, bal_adatok, jobb_adatok):
        """Mondathosszak kétvonalas grafikonja."""
        canvas.delete("all")
        canvas.update_idletasks()
        szel, mag = max(canvas.winfo_width(), 500), max(canvas.winfo_height(), 300)
        if not bal_adatok or not jobb_adatok:
            canvas.create_text(szel / 2, mag / 2, text=tr("Mindkét szövegben szükség van legalább egy mondatra."), fill="#666")
            return
        bal, jobb, felso, also = 55, 25, 42, 48
        szam = max(len(bal_adatok), len(jobb_adatok))
        maximum = max(1, max(bal_adatok + jobb_adatok))
        canvas.create_rectangle(bal, felso, szel - jobb, mag - also, outline="#b0b0b0")
        for i in range(5):
            y = felso + (mag - felso - also) * i / 4
            canvas.create_line(bal, y, szel - jobb, y, fill="#e5e5e5")
            canvas.create_text(bal - 7, y, text=f"{maximum * (1-i/4):.0f}", anchor="e", fill="#555")
        def pontok(adatok):
            return [(
                bal + (szel - bal - jobb) * i / max(1, szam - 1),
                mag - also - (mag - felso - also) * ertek / maximum
            ) for i, ertek in enumerate(adatok)]
        for adatok, szin in ((bal_adatok, "#3976b9"), (jobb_adatok, "#e4873a")):
            p = pontok(adatok)
            if len(p) == 1:
                x, y = p[0]; canvas.create_oval(x-3, y-3, x+3, y+3, fill=szin, outline="")
            else:
                canvas.create_line(*[koordinata for pont in p for koordinata in pont], fill=szin, width=2, smooth=True)
                for x, y in p: canvas.create_oval(x-3, y-3, x+3, y+3, fill=szin, outline="")
        canvas.create_text((bal + szel - jobb) / 2, mag - 18, text=tr("Mondat sorszáma"))
        canvas.create_text(12, (felso + mag - also) / 2, text=tr("Szó"), angle=90)
        canvas.create_line(bal, 19, bal+18, 19, fill="#3976b9", width=3); canvas.create_text(bal+24, 19, text=tr("Bal fájl"), anchor="w")
        canvas.create_line(bal+115, 19, bal+133, 19, fill="#e4873a", width=3); canvas.create_text(bal+139, 19, text=tr("Jobb fájl"), anchor="w")

    def reszletes_vizualizacio_ablak(self):
        """A szövegekhez tartozó, módszerspecifikus magyarázó grafikonok."""
        szoveg1 = self.text1.get("1.0", "end-1c")
        szoveg2 = self.text2.get("1.0", "end-1c")
        if not szoveg1.strip() or not szoveg2.strip():
            messagebox.showwarning(tr("Részletes vizualizáció"), tr("Mindkét szövegmezőnek tartalmaznia kell szöveget."))
            return

        _sw = stopszavak_a_szovegekhez(szoveg1, szoveg2)
        szavak1 = [s for s in re.findall(r"\w+", szoveg1.lower()) if len(s) > 1 and s not in _sw]
        szavak2 = [s for s in re.findall(r"\w+", szoveg2.lower()) if len(s) > 1 and s not in _sw]
        kozos = Counter(szavak1) & Counter(szavak2)
        kulcsszavak = [(szo, kozos[szo], Counter(szavak1)[szo], Counter(szavak2)[szo])
                        for szo in kozos]
        kulcsszavak.sort(key=lambda x: (-x[1], x[0]))
        kulcsszavak = kulcsszavak[:10]
        ritmus, hossz1, hossz2 = self._ritmus_elemzes(szoveg1, szoveg2)
        stat1, stat2 = self._stilisztikai_elemzes(szoveg1, szoveg2)
        ng1, ng2 = self._get_ngrams(szoveg1, 4), self._get_ngrams(szoveg2, 4)
        kozos_ngramok = sorted(" ".join(ng) for ng in ng1.intersection(ng2))[:100]
        # Itt szándékosan minden szó szerepel (a stop-szavak és az egybetűsek is),
        # mert ez a fül teljes szógyakorisági kimutatás, nem kulcsszó-elemzés.
        gyakorisag1 = Counter(re.findall(r"\w+", szoveg1.lower()))
        gyakorisag2 = Counter(re.findall(r"\w+", szoveg2.lower()))
        rendezett1 = sorted(gyakorisag1.items(), key=lambda elem: (-elem[1], elem[0]))
        rendezett2 = sorted(gyakorisag2.items(), key=lambda elem: (-elem[1], elem[0]))

        ablak = tk.Toplevel(self)
        ablak.title(tr("Részletes vizualizációk"))
        ablak.geometry("980x650")
        ablak.minsize(700, 460)
        ttk.Label(ablak, text=tr("A két dokumentum részletes, értelmezhető összehasonlítása"), font=("TkDefaultFont", 11, "bold")).pack(anchor="w", padx=12, pady=(10, 4))
        ful = ttk.Notebook(ablak)
        ful.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        f_kulcs = ttk.Frame(ful); ful.add(f_kulcs, text=tr("  Kulcsszavak  "))
        ttk.Label(f_kulcs, text=tr("A stop-szavak nélküli, mindkét szövegben előforduló legerősebb kulcsszavak.")).pack(anchor="w", padx=10, pady=8)
        kulcs_canvas = tk.Canvas(f_kulcs, background="white", highlightthickness=0); kulcs_canvas.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        kulcs_adat = [(szo, bal, jobb) for szo, _, bal, jobb in kulcsszavak]
        kulcs_canvas.bind("<Configure>", lambda e: self._rajzolj_osszehasonlito_savakat(kulcs_canvas, kulcs_adat))
        ablak.after(60, lambda: self._rajzolj_osszehasonlito_savakat(kulcs_canvas, kulcs_adat))

        f_ritmus = ttk.Frame(ful); ful.add(f_ritmus, text=tr("  Mondatritmus  "))
        ttk.Label(f_ritmus, text=tr(f"Mondatritmus-egyezés: {ritmus:.2f}%. A vonalak a mondatok szavainak számát mutatják.")).pack(anchor="w", padx=10, pady=8)
        ritmus_canvas = tk.Canvas(f_ritmus, background="white", highlightthickness=0); ritmus_canvas.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        ritmus_canvas.bind("<Configure>", lambda e: self._rajzolj_vonaldiagramot(ritmus_canvas, hossz1, hossz2))
        ablak.after(60, lambda: self._rajzolj_vonaldiagramot(ritmus_canvas, hossz1, hossz2))

        f_stil = ttk.Frame(ful); ful.add(f_stil, text=tr("  Stilisztika  "))
        ttk.Label(f_stil, text=tr("A nyers stilisztikai mutatók összehasonlítása (eltérő mértékegységek miatt elsősorban arányként értelmezendő). ")).pack(anchor="w", padx=10, pady=8)
        stil_canvas = tk.Canvas(f_stil, background="white", highlightthickness=0); stil_canvas.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        stil_adat = [(tr("Szavak"), stat1[0], stat2[0]), (tr("Egyedi szavak"), stat1[1], stat2[1]), ("TTR (%)", stat1[2], stat2[2]), (tr("Átl. szóhossz"), stat1[3], stat2[3]), (tr("Átl. mondathossz"), stat1[4], stat2[4])]
        stil_canvas.bind("<Configure>", lambda e: self._rajzolj_osszehasonlito_savakat(stil_canvas, stil_adat))
        ablak.after(60, lambda: self._rajzolj_osszehasonlito_savakat(stil_canvas, stil_adat))

        f_ngram = ttk.Frame(ful); ful.add(f_ngram, text=tr("  Közös N-gramok  "))
        ttk.Label(f_ngram, text=tr(f"Közös, egymást követő 4-szavas kifejezések: {len(kozos_ngramok)} db.")).pack(anchor="w", padx=10, pady=8)
        lista_keret = ttk.Frame(f_ngram); lista_keret.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        lista = tk.Listbox(lista_keret, font=("Consolas", 10)); lista.pack(side="left", fill="both", expand=True)
        gorgeto = ttk.Scrollbar(lista_keret, orient="vertical", command=lista.yview); gorgeto.pack(side="right", fill="y"); lista.configure(yscrollcommand=gorgeto.set)
        if kozos_ngramok:
            for ng in kozos_ngramok: lista.insert("end", ng)
        else:
            lista.insert("end", tr("Nincs közös 4-szavas kifejezés."))

        f_gyakorisag = ttk.Frame(ful); ful.add(f_gyakorisag, text=tr("  Szógyakoriság  "))
        ttk.Label(
            f_gyakorisag,
            text=tr(f"Minden szó kisbetűsítve szerepel; mindkét lista külön a leggyakoribb szóval kezdődik.  "
                  f"Bal: {sum(gyakorisag1.values())} szó, {len(gyakorisag1)} egyedi.  "
                  f"Jobb: {sum(gyakorisag2.values())} szó, {len(gyakorisag2)} egyedi.")
        ).pack(anchor="w", padx=10, pady=8)
        gyak_keret = ttk.Frame(f_gyakorisag)
        gyak_keret.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        oszlopok = ("bal_szo", "bal_db", "jobb_szo", "jobb_db")
        gyak_tree = ttk.Treeview(gyak_keret, columns=oszlopok, show="headings")
        gyak_tree.heading("bal_szo", text=tr("Bal fájl – szó"))
        gyak_tree.heading("bal_db", text=tr("Db"))
        gyak_tree.heading("jobb_szo", text=tr("Jobb fájl – szó"))
        gyak_tree.heading("jobb_db", text=tr("Db"))
        gyak_tree.column("bal_szo", width=290, anchor="w")
        gyak_tree.column("bal_db", width=70, anchor="center", stretch=False)
        gyak_tree.column("jobb_szo", width=290, anchor="w")
        gyak_tree.column("jobb_db", width=70, anchor="center", stretch=False)
        gorgeto = ttk.Scrollbar(gyak_keret, orient="vertical", command=gyak_tree.yview)
        gyak_tree.configure(yscrollcommand=gorgeto.set)
        gyak_tree.pack(side="left", fill="both", expand=True)
        gorgeto.pack(side="right", fill="y")
        for i in range(max(len(rendezett1), len(rendezett2))):
            bal_szo, bal_db = rendezett1[i] if i < len(rendezett1) else ("", "")
            jobb_szo, jobb_db = rendezett2[i] if i < len(rendezett2) else ("", "")
            gyak_tree.insert("", "end", values=(bal_szo, bal_db, jobb_szo, jobb_db))

        def reszletes_vizualizacio_html_mentes():
            cel_utvonal = filedialog.asksaveasfilename(
                title=tr("Részletes vizualizáció HTML mentése"),
                defaultextension=".html",
                filetypes=[("HTML fájlok", "*.html"), ("Minden fájl", "*.*")]
            )
            if not cel_utvonal:
                return
            try:
                reszletes_vizualizacio_html_riport_generalasa(
                    self.cimke1_var.get(), self.cimke2_var.get(),
                    kulcs_adat, ritmus, hossz1, hossz2, stil_adat,
                    kozos_ngramok, rendezett1, rendezett2, cel_utvonal
                )
                messagebox.showinfo(tr("Siker"), tr(f"Részletes vizualizációs HTML riport elmentve:\n{cel_utvonal}"))
                webbrowser.open(f"file://{os.path.abspath(cel_utvonal)}")
            except Exception as e:
                messagebox.showerror(tr("Hiba"), tr(f"Nem sikerült létrehozni a részletes vizualizációs HTML riportot:\n{e}"))

        also_keret = ttk.Frame(ablak, padding=10)
        also_keret.pack(side="bottom", fill="x")
        ttk.Button(also_keret, text=tr("💾 Mentés HTML fájlba..."), command=reszletes_vizualizacio_html_mentes).pack(side="left", padx=5)
        ttk.Button(also_keret, text=tr("✕ Bezár"), command=ablak.destroy).pack(side="right", padx=5)

        self.statusz_var.set(tr("Részletes vizualizáció elkészült."))

    def osszehasonlitas(self):
        szoveg1 = self.text1.get("1.0", "end-1c")
        szoveg2 = self.text2.get("1.0", "end-1c")

        for t in (self.text1, self.text2):
            t.tag_remove("elter", "1.0", "end")
            t.tag_remove("sor_elter", "1.0", "end")
            t.tag_remove("egyezes", "1.0", "end")
            for tag in list(t.tag_names()):
                if tag == "hdiff_kijelolt":
                    t.tag_remove(tag, "1.0", "end")
                elif tag.startswith("hdiff_"):
                    # Egyedi, futásonként újra létrehozott blokk-tag - ne csak a
                    # tartományát töröljük, hanem magát a tag-definíciót (a
                    # kötésekkel együtt) is, különben minden újabb Start
                    # futtatásnál egyre több (soha nem takarított) tag halmozódna
                    # fel a widgetben, ami idővel jelentősen lelassítja a szöveg
                    # beszúrását/renderelését.
                    t.tag_delete(tag)
        self._hagyomanyos_diff_blokkok = []
        self._hdiff_aktiv_index = -1
        if hasattr(self, "hdiff_szamlalo_var"):
            self.hdiff_szamlalo_var.set("")

        if not szoveg1 and not szoveg2:
            self.statusz_var.set(tr("Mindkét fájl üres."))
            return

        self.statusz_var.set(tr("Háttérszámolás folyamatban..."))
        self._mozgasjelzo_inditasa(tr("Elemzés folyamatban…"))
        self.update_idletasks()

        tipus = untr(self.ellenorzes_tipus_var.get())
        szokoz_ki = self.szokoz_ki_var.get()
        irasjel_ki = self.irasjel_ki_var.get()

        def hatter_szamolas():
            try:
                if tipus.startswith("Winnowing"):
                    win_ertek = self._winnowing_similarity(szoveg1, szoveg2)
                    self.after(0, lambda: self._winnowing_eredmeny_megjelenites(win_ertek))

                elif tipus.startswith("TF-IDF"):
                    tfidf_ertek = self._tfidf_cosine_similarity(szoveg1, szoveg2)
                    self.after(0, lambda: self._tfidf_eredmeny_megjelenites(tfidf_ertek))

                elif tipus.startswith("Mondatritmus"):
                    ritmus_szazalek, l1, l2 = self._ritmus_elemzes(szoveg1, szoveg2)
                    self.after(0, lambda: self._ritmus_eredmeny_megjelenites(ritmus_szazalek, len(l1), len(l2)))

                elif tipus.startswith("Hagyományos"):
                    s1, terkep1 = self._szoveg_tisztitas_terkeppel(szoveg1, szokoz_ki, irasjel_ki)
                    s2, terkep2 = self._szoveg_tisztitas_terkeppel(szoveg2, szokoz_ki, irasjel_ki)

                    opkodok, hasonlosag = karakter_diff_elemzes(s1, s2)
                    elter_karakter = 0
                    blokkok = []
                    for tag, i1, i2, j1, j2 in opkodok:
                        if tag == "equal":
                            # Csak akkor jelöljük egyezésnek, ha tartalmaz legalább
                            # egy nem-whitespace karaktert - egy csupa szóköz/sortörés
                            # szakasz "egyezése" technikailag igaz, de tartalmilag
                            # semmitmondó, és csak összezavarja a képet.
                            if i2 > i1 and s1[i1:i2].strip():
                                o1_start, o1_end = terkep1[i1], terkep1[i2 - 1] + 1
                                o2_start, o2_end = terkep2[j1], terkep2[j2 - 1] + 1
                                szoszam = len(szoveg1[o1_start:o1_end].split())
                                blokkok.append({
                                    "id": len(blokkok) + 1,
                                    "start1": o1_start, "end1": o1_end,
                                    "start2": o2_start, "end2": o2_end,
                                    "jelentos": szoszam >= MIN_HDIFF_SZAVAK,
                                })
                        else:
                            elter_karakter += max(i2 - i1, j2 - j1)

                    self.after(0, lambda: self._alkalmaz_diff_eredmenyt(elter_karakter, len(s1), len(s2), hasonlosag, blokkok, bool(szokoz_ki or irasjel_ki)))

                elif tipus.startswith("N-gram"):
                    ng1 = self._get_ngrams(szoveg1, n=4)
                    ng2 = self._get_ngrams(szoveg2, n=4)
                    if not ng1 or not ng2:
                        self.after(0, lambda: self._rogzito_uzenet("Túl rövidek a szövegek az N-gram vizsgálathoz."))
                        return
                    
                    kozosen = ng1.intersection(ng2)
                    osszesen = ng1.union(ng2)
                    ngram_szazalek = (len(kozosen) / len(osszesen)) * 100 if osszesen else 0.0
                    self.after(0, lambda: self._ngram_eredmeny_megjelenites(ngram_szazalek, len(kozosen)))

                elif tipus.startswith("Szókészlet"):
                    cosine_ertek = self._cosine_similarity(szoveg1, szoveg2)
                    self.after(0, lambda: self._cosine_eredmeny_megjelenites(cosine_ertek))

                elif tipus.startswith("Jaccard"):
                    jaccard_ertek = self._jaccard_similarity(szoveg1, szoveg2)
                    self.after(0, lambda: self._jaccard_eredmeny_megjelenites(jaccard_ertek))

                elif tipus.startswith("Stilisztikai"):
                    st1, st2 = self._stilisztikai_elemzes(szoveg1, szoveg2)
                    self.after(0, lambda: self._stilisztikai_eredmeny_megjelenites(st1, st2))

                elif tipus.startswith("Simhash"):
                    simhash_ertek_ = simhash_hasonlosag(szoveg1, szoveg2)
                    self.after(0, lambda: self._simhash_eredmeny_megjelenites(simhash_ertek_))

            except Exception as e:
                self.after(0, lambda: messagebox.showerror(tr("Hiba"), str(e)))
            finally:
                self.after(0, self._mozgasjelzo_leallitasa)

        threading.Thread(target=hatter_szamolas, daemon=True).start()

    def minden_elemzes_ablak(self):
        szoveg1 = self.text1.get("1.0", "end-1c")
        szoveg2 = self.text2.get("1.0", "end-1c")

        if not szoveg1.strip() or not szoveg2.strip():
            messagebox.showwarning(tr("Figyelem"), tr("Mindkét szövegmezőnek tartalmaznia kell szöveget az összesítő futtatásához!"))
            return

        ablak = tk.Toplevel(self)
        ablak.title(tr("Átfogó Összehasonlító & Hasonlósági Index Jelentés"))
        ablak.geometry("950x660")
        ablak.minsize(750, 480)

        cimke = ttk.Label(ablak, text=tr("Minden elemzési modul eredménye és az összesített hasonlósági index:"), font=("TkDefaultFont", 11, "bold"))
        cimke.pack(side="top", anchor="w", padx=15, pady=10)

        belso_notebook = ttk.Notebook(ablak)
        belso_notebook.pack(side="top", fill="both", expand=True, padx=10, pady=(0, 5))

        ful_tabla = ttk.Frame(belso_notebook)
        belso_notebook.add(ful_tabla, text=tr("  📋 Táblázat  "))

        ful_grafikon = ttk.Frame(belso_notebook)
        belso_notebook.add(ful_grafikon, text=tr("  📊 Grafikon  "))

        tabla_keret = ttk.Frame(ful_tabla, padding=10)
        tabla_keret.pack(side="top", fill="both", expand=True)

        oszlopok = ("modul", "eredetem", "ertekeles")
        tree = ttk.Treeview(tabla_keret, columns=oszlopok, show="headings", selectmode="browse")
        
        tree.heading("modul", text=tr("Vizsgálati Módszer / Metrika"))
        tree.heading("eredetem", text=tr("Mért Érték (%)"))
        tree.heading("ertekeles", text=tr("Minősítés / Részletes Értékelés"))

        tree.column("modul", width=220, anchor="w")
        tree.column("eredetem", width=130, anchor="center")
        tree.column("ertekeles", width=520, anchor="w")

        scrollbar = ttk.Scrollbar(tabla_keret, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=scrollbar.set)

        tree.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        grafikon_canvas = tk.Canvas(ful_grafikon, background="white", highlightthickness=0)
        grafikon_canvas.pack(side="top", fill="both", expand=True, padx=10, pady=10)

        # Számítások
        win_ertek = self._winnowing_similarity(szoveg1, szoveg2)
        tfidf_ertek = self._tfidf_cosine_similarity(szoveg1, szoveg2)
        ritmus_szaz, l1, l2 = self._ritmus_elemzes(szoveg1, szoveg2)
        
        diff_szaz = karakter_diff_arany(szoveg1, szoveg2)
        
        ng1 = self._get_ngrams(szoveg1, 4)
        ng2 = self._get_ngrams(szoveg2, 4)
        ngram_szaz = (len(ng1.intersection(ng2)) / len(ng1.union(ng2))) * 100 if ng1 and ng2 else 0.0

        cosine_ertek = self._cosine_similarity(szoveg1, szoveg2)
        jaccard_ertek = self._jaccard_similarity(szoveg1, szoveg2)
        st1, st2 = self._stilisztikai_elemzes(szoveg1, szoveg2)
        simhash_ertek_ = simhash_hasonlosag(szoveg1, szoveg2)

        # Súlyozott összesített szöveghasonlósági index (%)
        osszesitett_szaz = (
            win_ertek * 0.35 +
            tfidf_ertek * 0.25 +
            ngram_szaz * 0.20 +
            diff_szaz * 0.10 +
            ritmus_szaz * 0.10
        )

        if osszesitett_szaz < 15:
            osszesitett_minosites = tr("Alacsony / Csekély szöveghasonlóság")
            szin_stilus = "#006600"
        elif osszesitett_szaz < 35:
            osszesitett_minosites = tr("Mérsékelt / Hasonló téma vagy részbeni átfedés")
            szin_stilus = "#b37700"
        else:
            osszesitett_minosites = tr("MAGAS / ERŐS SZÖVEGEGYEZÉS")
            szin_stilus = "#cc0000"

        adatok = [
            ("Winnowing Ujjlenyomat", f"{win_ertek:.2f}%", "Ujjlenyomat-alapú szövegegyezés-vizsgálat (átrendezésbiztos)"),
            ("TF-IDF Súlyozott Tartalmi Elemzés", f"{tfidf_ertek:.2f}%", "Ritka szavak súlyozása alapú precíz tematikus egyezés"),
            ("N-gram (4-szavas) Kifejezés", f"{ngram_szaz:.2f}%", "Közös fix 4-szavas kifejezések aránya"),
            ("Mondatritmus & Parafrázis", f"{ritmus_szaz:.2f}%", f"Mondathossz ritmusprofil | Mondatok: {len(l1)} vs {len(l2)}"),
            ("Hagyományos Karakter Diff", f"{diff_szaz:.2f}%", "Közvetlen karakteres egyezési arány"),
            ("Szókészlet (Cosine)", f"{cosine_ertek:.2f}%", "Stop-szűrt alap szókészlet egyezése"),
            ("Jaccard Halmaz-hasonlóság", f"{jaccard_ertek:.2f}%", "Egyedi szavak halmaz-átfedése"),
            ("Stilisztika (Bal fájl TTR)", f"{st1[2]:.2f}%", f"Szó: {st1[0]} db, Egyedi: {st1[1]} db, Átl. mondat: {st1[4]:.1f} szó"),
            ("Stilisztika (Jobb fájl TTR)", f"{st2[2]:.2f}%", f"Szó: {st2[0]} db, Egyedi: {st2[1]} db, Átl. mondat: {st2[4]:.1f} szó"),
            ("Simhash Ujjlenyomat", f"{simhash_ertek_:.2f}%", "Nyelvfüggetlen, Hamming-távolság alapú gyors ujjlenyomat-egyezés"),
        ]

        adatok = [(tr(nev), ertek, tr(leiras)) for nev, ertek, leiras in adatok]

        for item in adatok:
            tree.insert("", "end", values=item)

        grafikon_adatok = [(nev, float(ertek.replace('%', '')) if '%' in ertek else 0.0) for nev, ertek, _ in adatok]
        ablak.after(50, lambda: sav_diagram_rajzolasa(grafikon_canvas, grafikon_adatok))
        grafikon_canvas.bind("<Configure>", lambda e: sav_diagram_rajzolasa(grafikon_canvas, grafikon_adatok))

        eredmeny_keret = ttk.LabelFrame(ablak, text=tr(" 🎯 Súlyozott Összesített Szöveghasonlósági Index "), padding=12)
        eredmeny_keret.pack(side="top", fill="x", padx=10, pady=5)

        szoveg_lbl = f"{tr('Átfogó Súlyozott Index: ')}{osszesitett_szaz:.2f}%  —  {osszesitett_minosites}"
        lbl_eredmeny = tk.Label(eredmeny_keret, text=szoveg_lbl, font=("TkDefaultFont", 12, "bold"), fg=szin_stilus)
        lbl_eredmeny.pack(side="left", padx=5)

        also_keret = ttk.Frame(ablak, padding=10)
        also_keret.pack(side="bottom", fill="x")

        def jelentes_mentes():
            fajl_utv = filedialog.asksaveasfilename(
                title=tr("Átfogó jelentés mentése"),
                defaultextension=".txt",
                filetypes=[("Szövegfájlok", "*.txt"), ("Minden fájl", "*.*")]
            )
            if not fajl_utv:
                return
            try:
                with open(fajl_utv, "w", encoding="utf-8") as out:
                    out.write(tr("=== SABTEXTCOMPAR - SZÖVEGHASONLÓSÁGI JELENTÉS ===") + "\n")
                    out.write(f"{tr('Bal fájl')}: {self.cimke1_var.get()}\n")
                    out.write(f"{tr('Jobb fájl')}: {self.cimke2_var.get()}\n")
                    out.write("=" * 65 + "\n")
                    out.write(f"{tr('ÖSSZESÍTETT SZÖVEGHASONLÓSÁGI / EGYEZÉSI INDEX: ')}{osszesitett_szaz:.2f}%\n")
                    out.write(f"{tr('MINŐSÍTÉS: ')}{osszesitett_minosites}\n")
                    out.write("=" * 65 + "\n\n")
                    for row_id in tree.get_children():
                        vals = tree.item(row_id, "values")
                        out.write(f"{tr('Módszer: ')}{vals[0]}\n")
                        out.write(f"{tr('Érték:   ')}{vals[1]}\n")
                        out.write(f"{tr('Elemzés: ')}{vals[2]}\n")
                        out.write("-" * 40 + "\n")
                messagebox.showinfo(tr("Siker"), tr(f"A jelentést sikeresen elmentettük ide:\n{fajl_utv}"))
            except Exception as ex:
                messagebox.showerror(tr("Hiba"), tr(f"Nem sikerült menteni a jelentést:\n{ex}"))

        def html_riport_ez_ablakbol():
            cel_utvonal = filedialog.asksaveasfilename(
                title=tr("HTML riport mentése"),
                defaultextension=".html",
                filetypes=[("HTML fájlok", "*.html"), ("Minden fájl", "*.*")]
            )
            if not cel_utvonal:
                return
            try:
                html_riport_generalasa(self.cimke1_var.get(), szoveg1, self.cimke2_var.get(), szoveg2, cel_utvonal)
                messagebox.showinfo(tr("Siker"), tr(f"HTML riport elmentve:\n{cel_utvonal}"))
                webbrowser.open(f"file://{os.path.abspath(cel_utvonal)}")
            except Exception as e:
                messagebox.showerror(tr("Hiba"), tr(f"Nem sikerült létrehozni a HTML riportot:\n{e}"))

        ttk.Button(also_keret, text=tr("💾 Teljes Jelentés Mentése Fájlba..."), command=jelentes_mentes).pack(side="left", padx=5)
        ttk.Button(also_keret, text=tr("🌐 HTML Riport"), command=html_riport_ez_ablakbol).pack(side="left", padx=5)
        ttk.Button(also_keret, text=tr("Bezárás"), command=ablak.destroy).pack(side="right", padx=5)

    def _winnowing_eredmeny_megjelenites(self, ertek):
        self.statusz_var.set(tr(f"[Winnowing] Ujjlenyomat egyezés: {ertek:.2f}%"))
        
        if ertek < 15:
            minosites = tr("Alacsony / Önálló szövegek.")
        elif ertek < 40:
            minosites = tr("Közepes egyezés vagy részleges átvétel.")
        else:
            minosites = tr("MAGAS / ERŐS SZÖVEGEGYEZÉS (Winnowing ujjlenyomat)")

        messagebox.showinfo(
            tr("Winnowing szövegegyezés-vizsgálat"),
            f"A dokumentumok ujjlenyomatának egyezése:\n\n"
            f" >> {ertek:.2f}% <<\n\n"
            f"ÉRTÉKELÉS: {minosites}\n\n"
            f"MIT MÉR? A szavakból képzett rövid, egymást követő szókapcsolatok "
            f"(ujjlenyomatok) közös arányát.\n\n"
            f"MIÉRT HASZNOS? Kisebb beszúrások vagy a bekezdések átrendezése kevésbé "
            f"torzítja, ezért jó átvett szövegrészek előszűrésére.\n\n"
            f"FONTOS: A százalék nem szó szerinti egyezési arány és önmagában nem bizonyít másolást vagy szerzői jogsértést; "
            f"a találatokat a vizuális egyezésnézetben érdemes ellenőrizni."
        )

    def _tfidf_eredmeny_megjelenites(self, ertek):
        self.statusz_var.set(tr(f"[TF-IDF] Tartalmi egyezés: {ertek:.2f}%"))
        messagebox.showinfo(
            tr("TF-IDF Tartalmi Elemzés"),
            f"A ritka szavakkal súlyozott TF-IDF egyezés:\n\n"
            f" >> {ertek:.2f}% <<\n\n"
            f"MIT MÉR? A ritkább, tartalmi szavak közös jelenlétét és gyakoriságát. "
            f"A nagyon általános stop-szavak (pl. „és”, „a”, „hogy”) nem kapnak súlyt.\n\n"
            f"HOGYAN ÉRTELMEZD? Magas érték rendszerint közös témára vagy közös kulcsfogalmakra utal. "
            f"A szavak sorrendje és a mondatok jelentése nem része a mérésnek.\n\n"
            f"FONTOS: Azonos témájú, de önálló szövegek is kaphatnak magas értéket."
        )

    def _ritmus_eredmeny_megjelenites(self, szazalek, db1, db2):
        self.statusz_var.set(tr(f"[Mondatritmus] Struktúra egyezés: {szazalek:.2f}% (Mondatok: {db1} vs {db2})"))
        if szazalek < 15:
            minosites = tr("Alacsony / Eltérő mondatszerkezet.")
        elif szazalek < 40:
            minosites = tr("Közepes szerkezeti hasonlóság.")
        else:
            minosites = tr("MAGAS / ERŐS SZÖVEGEGYEZÉS (Mondatritmus egyezés)")
        messagebox.showinfo(
            tr("Mondatritmus & Parafrázis Eredmény"),
            f"A két szöveg mondathossz-ritmusának egyezése:\n\n"
            f" >> {szazalek:.2f}% <<\n\n"
            f"Bal fájl mondatainak száma: {db1} db\n"
            f"Jobb fájl mondatainak száma: {db2} db\n\n"
            f"ÉRTÉKELÉS: {minosites}\n\n"
            f"Ez a módszer a mondatok hosszát (szavak száma) hasonlítja "
            f"össze — ha valaki parafrázissal másol, a szavak másak lehetnek, "
            f"de a mondathossz ritmusa gyakran hasonló marad.\n\n"
            f"MIT NEM MÉR? Nem vizsgálja a közös szavakat vagy a mondatok jelentését, csak a szerkezetet. "
            f"Az érték ezért jelzés, nem önálló bizonyíték."
        )

    def _alkalmaz_diff_eredmenyt(self, elter_karakter, len1, len2, hasonlosag, blokkok, tisztitott=False):
        self._hagyomanyos_diff_tagek_alkalmazasa(blokkok)
        self.statusz_var.set(tr(f"[Diff] Eltérés: {elter_karakter} karakter | Egyezés: {hasonlosag:.2f}%"))
        if hasonlosag < 15:
            minosites = tr("Alacsony / Önálló szövegek.")
        elif hasonlosag < 40:
            minosites = tr("Közepes egyezés vagy részleges átvétel.")
        else:
            minosites = tr("MAGAS / ERŐS SZÖVEGEGYEZÉS")
        messagebox.showinfo(
            tr("Hagyományos Diff Eredmény"),
            f"A két szöveg karakteres egyezési aránya:\n\n"
            f" >> {hasonlosag:.2f}% <<\n\n"
            f"Eltérő karakterek száma: {elter_karakter} db\n"
            f"Bal fájl hossza: {len1} karakter | Jobb fájl hossza: {len2} karakter\n\n"
            f"ÉRTÉKELÉS: {minosites}\n\n"
            + (f"FIGYELEM: az érték a szóközök/írásjelek NÉLKÜL számolt szövegre vonatkozik, "
               f"ezért eltérhet az Összesítő Táblától és a HTML riporttól (azok a teljes szöveget vizsgálják).\n\n" if tisztitott else "")
            + f"Ez a módszer a legegyszerűbb, közvetlen karakter-egyezést vizsgál — "
            f"átrendezésre vagy parafrázisra nem érzékeny.\n\n"
            f"MIT MÉR? Betűket, szóközöket és írásjeleket hasonlít össze a szöveg eredeti sorrendjében. "
            f"Ezért szó szerinti vagy közel szó szerinti másolatoknál a leghasznosabb."
        )

    def _hagyomanyos_diff_tagek_alkalmazasa(self, blokkok):
        for t in (self.text1, self.text2):
            t.tag_remove("egyezes", "1.0", "end")
            for tag in list(t.tag_names()):
                if tag == "hdiff_kijelolt":
                    t.tag_remove(tag, "1.0", "end")
                elif tag.startswith("hdiff_"):
                    t.tag_delete(tag)

        paletta = SZINEK["diff_paletta"]
        jelentos_blokkok = []
        for bl in blokkok:
            if bl.get("jelentos"):
                uj_id = len(jelentos_blokkok) + 1
                bl = dict(bl, id=uj_id)
                jelentos_blokkok.append(bl)
                tagnev = f"hdiff_{uj_id}"
                szin = paletta[(uj_id - 1) % len(paletta)]
                for t in (self.text1, self.text2):
                    t.tag_configure(tagnev, background=szin, foreground=szin_kontraszt(szin))
                    t.tag_bind(tagnev, "<Button-1>",
                               lambda event, b=bl, panel=t: self._hagyomanyos_diff_ugras_blokkra(b, panel))
                    t.tag_bind(tagnev, "<Enter>", lambda event, tw=t: tw.configure(cursor="hand2"))
                    t.tag_bind(tagnev, "<Leave>", lambda event, tw=t: tw.configure(cursor="xterm"))
                self.text1.tag_add(tagnev, f"1.0+{bl['start1']}c", f"1.0+{bl['end1']}c")
                self.text2.tag_add(tagnev, f"1.0+{bl['start2']}c", f"1.0+{bl['end2']}c")
            else:
                # Rövid (< MIN_HDIFF_SZAVAK szavas) egyezés: csak sima, nem
                # kattintható zöld kiemelés - ide szándékosan nem kötünk ugrást,
                # mert a globális karakteres illesztés ilyen rövid, gyakori
                # szavaknál nem feltétlenül az "igazi", kontextusban odaillő
                # párt találná meg a másik oldalon.
                self.text1.tag_add("egyezes", f"1.0+{bl['start1']}c", f"1.0+{bl['end1']}c")
                self.text2.tag_add("egyezes", f"1.0+{bl['start2']}c", f"1.0+{bl['end2']}c")

        for t in (self.text1, self.text2):
            t.tag_raise("hdiff_kijelolt")

        self._hagyomanyos_diff_blokkok = jelentos_blokkok
        self._hdiff_aktiv_index = -1

        if jelentos_blokkok:
            self.hdiff_szamlalo_var.set(
                tr(f"{len(jelentos_blokkok)} egyértelmű (≥{MIN_HDIFF_SZAVAK} szavas) egyezés "
                   f"(kattints egy kiemelt szakaszra az ugráshoz)"))
        else:
            self.hdiff_szamlalo_var.set(tr("Nincs elég hosszú, egyértelmű egyezés."))

    def _hagyomanyos_diff_ugras_blokkra(self, blokk, forras_panel=None):
        # Az "aktív" panel az, amit a felhasználó épp néz/használ (amire
        # kattintott, vagy - gombos navigációnál - amelyikbe legutóbb
        # kattintott/fókuszált). Csak a SZEMKÖZTI (másik) panelt görgetjük -
        # az aktívat, amit már úgyis lát, nem mozdítjuk el alóla.
        aktiv = forras_panel if forras_panel is not None else (self._aktiv_diff_panel or self.text1)
        self._aktiv_diff_panel = aktiv
        szemkozti = self.text2 if aktiv is self.text1 else self.text1

        for t in (self.text1, self.text2):
            t.tag_remove("hdiff_kijelolt", "1.0", "end")
        s1 = f"1.0+{blokk['start1']}c"
        e1 = f"1.0+{blokk['end1']}c"
        s2 = f"1.0+{blokk['start2']}c"
        e2 = f"1.0+{blokk['end2']}c"
        self.text1.tag_add("hdiff_kijelolt", s1, e1)
        self.text2.tag_add("hdiff_kijelolt", s2, e2)
        for t in (self.text1, self.text2):
            t.tag_raise("hdiff_kijelolt")

        if szemkozti is self.text1:
            self._blokk_lathatova_tetele(self.text1, s1, e1)
        else:
            self._blokk_lathatova_tetele(self.text2, s2, e2)

        self._hdiff_aktiv_index = blokk["id"] - 1
        self.hdiff_szamlalo_var.set(
            tr(f"Egyezés {blokk['id']}/{len(self._hagyomanyos_diff_blokkok)} "
               f"({blokk['end1'] - blokk['start1']} karakter)"))

    def _blokk_lathatova_tetele(self, widget, start_index, end_index):
        """A megadott tartományt úgy hozza láthatóvá, hogy - amennyire
        lehetséges - a látható terület KÖZEPÉRE kerüljön, ne csak épp annyira
        legyen görgetve, hogy egyetlen karaktere lógjon be a szél mentén (ahogy
        az egyszerű Text.see() tenné). Ez azért fontos, mert a panelek
        wrap="word" beállításúak, így egy hosszabb egyező szakasz több
        megjelenített sorra is törhet - see() önmagában könnyen a látható
        terület aljára/tetejére tenné úgy, hogy a szakasz nagy része kívül
        maradna."""
        widget.update_idletasks()
        try:
            kezdo_sor = int(str(widget.index(start_index)).split(".")[0])
            veg_sor = int(str(widget.index(end_index)).split(".")[0])
            kozep_sor = (kezdo_sor + veg_sor) / 2
            osszes_sor = max(1, int(str(widget.index("end-1c")).split(".")[0]))
            felso, also = widget.yview()
            lathato_arany = max(also - felso, 0.02)
            cel_arany = (kozep_sor - 1) / osszes_sor
            uj_felso = max(0.0, min(cel_arany - lathato_arany / 2, 1.0 - lathato_arany))
            widget.yview_moveto(uj_felso)
        except (tk.TclError, ValueError, ZeroDivisionError):
            pass
        # Biztonsági háló: a fenti becslés a logikai (nem a tördelt/megjelenített)
        # sorszámokkal dolgozik, ezért a see()-vel még rásegítünk mindkét
        # végpontra - ez csak akkor görget, ha valamelyik végpont mégsem
        # látszana, a középre igazítást nem rontja el.
        widget.see(start_index)
        widget.see(end_index)

    def _hagyomanyos_diff_kovetkezo(self):
        blokkok = self._hagyomanyos_diff_blokkok
        if not blokkok:
            return
        uj_index = (self._hdiff_aktiv_index + 1) % len(blokkok)
        self._hagyomanyos_diff_ugras_blokkra(blokkok[uj_index])

    def _hagyomanyos_diff_elozo(self):
        blokkok = self._hagyomanyos_diff_blokkok
        if not blokkok:
            return
        uj_index = (self._hdiff_aktiv_index - 1) % len(blokkok)
        self._hagyomanyos_diff_ugras_blokkra(blokkok[uj_index])

    def _rogzito_uzenet(self, szoveg):
        self.statusz_var.set(tr(szoveg))
        messagebox.showinfo(tr("Információ"), tr(szoveg))

    def _ngram_eredmeny_megjelenites(self, szazalek, kozos_db):
        self.statusz_var.set(tr(f"[N-gram] Egyezés: {szazalek:.2f}%"))
        if szazalek < 15:
            minosites = tr("Alacsony / Önálló szövegek.")
        elif szazalek < 40:
            minosites = tr("Közepes egyezés vagy részleges átvétel.")
        else:
            minosites = tr("MAGAS / ERŐS SZÖVEGEGYEZÉS")
        messagebox.showinfo(
            tr("N-gram Kifejezés Eredmény"),
            f"A két szöveg 4-szavas kifejezés-egyezése:\n\n"
            f" >> {szazalek:.2f}% <<\n\n"
            f"Közös 4-szavas kifejezések száma: {kozos_db} db\n\n"
            f"ÉRTÉKELÉS: {minosites}\n\n"
            f"Ez a módszer fix 4-szavas kifejezéseket keres — ha a szerző "
            f"több egymást követő szót változatlanul átemelt, azt ez felismeri.\n\n"
            f"MIT MÉR? Az egyedi, közös 4-szavas sorozatok arányát; a szógyakoriságot nem számolja külön. "
            f"A „Egyezések vizuális nézete” ablakban a minimális pontos egyezés hossza 2–10 szó között állítható."
        )

    def _cosine_eredmeny_megjelenites(self, ertek):
        self.statusz_var.set(tr(f"[Cosine] Hasonlóság: {ertek:.2f}%"))
        if ertek < 15:
            minosites = tr("Alacsony / Önálló szókészlet.")
        elif ertek < 40:
            minosites = tr("Közepes szókészlet-átfedés.")
        else:
            minosites = tr("MAGAS / ERŐS SZÖVEGEGYEZÉS")
        messagebox.showinfo(
            tr("Szókészlet (Cosine) Hasonlóság Eredmény"),
            f"A két dokumentum szókészletének koszinusz hasonlósága:\n\n"
            f" >> {ertek:.2f}% <<\n\n"
            f"ÉRTÉKELÉS: {minosites}\n\n"
            f"Ez a mutató a stop-szavak kiszűrése után a megmaradó "
            f"tartalmi szavak vektoriális egyezését méri — a szavak "
            f"előfordulási gyakorisága alapján.\n\n"
            f"HOGYAN ÉRTELMEZD? Akkor magas, ha hasonló tartalmi szavak hasonló arányban fordulnak elő. "
            f"A szavak sorrendjét és a pontos idézeteket nem keresi."
        )

    def _jaccard_eredmeny_megjelenites(self, ertek):
        self.statusz_var.set(tr(f"[Jaccard] Hasonlóság: {ertek:.2f}%"))
        if ertek < 15:
            minosites = tr("Alacsony / Önálló szókészlet.")
        elif ertek < 40:
            minosites = tr("Közepes halmaz-átfedés.")
        else:
            minosites = tr("MAGAS / ERŐS SZÖVEGEGYEZÉS")
        messagebox.showinfo(
            tr("Jaccard Halmaz-hasonlóság Eredmény"),
            f"A két szöveg egyedi szavainak halmaz-átfedése:\n\n"
            f" >> {ertek:.2f}% <<\n\n"
            f"ÉRTÉKELÉS: {minosites}\n\n"
            f"Ez a módszer az egyedi szavak halmazát hasonlítja össze — "
            f"a szavak gyakoriságát nem veszi figyelembe, csak azt, hogy "
            f"mely szavak szerepelnek mindkét dokumentumban.\n\n"
            f"PÉLDA: Egy százszor leírt szó ugyanannyit számít, mint egy egyszer szereplő szó. "
            f"A sorrendet és a mondatok jelentését sem vizsgálja."
        )

    def _stilisztikai_eredmeny_megjelenites(self, st1, st2):
        self.statusz_var.set(tr("Stilisztikai elemzés elkészült."))
        messagebox.showinfo(
            tr("Stilisztikai Elemzés Eredmény"),
            f"A két szöveg stilisztikai profilja:\n\n"
            f"BAL FÁJL:\n"
            f"  Összes szó: {st1[0]} db | Egyedi szó: {st1[1]} db\n"
            f"  TTR (szókincsgazdagság): {st1[2]:.2f}%\n"
            f"  Átlagos szóhossz: {st1[3]:.1f} karakter\n"
            f"  Átlagos mondat hossz: {st1[4]:.1f} szó\n\n"
            f"JOBB FÁJL:\n"
            f"  Összes szó: {st2[0]} db | Egyedi szó: {st2[1]} db\n"
            f"  TTR (szókincsgazdagság): {st2[2]:.2f}%\n"
            f"  Átlagos szóhossz: {st2[3]:.1f} karakter\n"
            f"  Átlagos mondat hossz: {st2[4]:.1f} szó\n\n"
            f"A TTR (Type-Token Ratio) azt mutatja, hogy a szöveg mennyire "
            f"változatos szókincset használ — magasabb érték gazdagabb, "
            f"alacsonyabb érték ismétlődőbb szókincset jelent.\n\n"
            f"MIT MÉR? Nem tartalmi egyezést vagy másolást, hanem két külön szöveg stílusjegyeit. "
            f"A különbségek a szerzői hangról, műfajról vagy szöveghosszról is adódhatnak."
        )

    def _simhash_eredmeny_megjelenites(self, ertek):
        self.statusz_var.set(tr(f"[Simhash] Ujjlenyomat egyezés: {ertek:.2f}%"))
        messagebox.showinfo(
            tr("Simhash Ujjlenyomat Eredmény"),
            f"A dokumentumok Simhash-ujjlenyomatának egyezése:\n\n"
            f" >> {ertek:.2f}% <<\n\n"
            f"MIT MÉR? A szavak és szógyakoriságok teljes szövegszintű mintázatából "
            f"egy 64 bites ujjlenyomatot készít, majd e két ujjlenyomat biteltérését méri "
            f"(Hamming-távolság).\n\n"
            f"HOGYAN ÉRTELMEZD? Magas érték hasonló általános szóhasználatra utal, de NEM azt jelenti, "
            f"hogy a szövegek ennyi százalékban szó szerint azonosak. Gyors előszűrésre való, "
            f"és nem mutatja meg az egyezések helyét."
        )



    def html_riport_general(self):
        szoveg1 = self.text1.get("1.0", "end-1c")
        szoveg2 = self.text2.get("1.0", "end-1c")
        if not szoveg1.strip() or not szoveg2.strip():
            messagebox.showwarning(tr("Figyelem"), "Mindkét szövegmezőnek tartalmaznia kell szöveget a HTML riporthoz!")
            return

        cel_utvonal = filedialog.asksaveasfilename(
            title=tr("HTML riport mentése"),
            defaultextension=".html",
            filetypes=[("HTML fájlok", "*.html"), ("Minden fájl", "*.*")]
        )
        if not cel_utvonal:
            return

        cimke1 = self.cimke1_var.get()
        cimke2 = self.cimke2_var.get()
        try:
            html_riport_generalasa(cimke1, szoveg1, cimke2, szoveg2, cel_utvonal)
            messagebox.showinfo(tr("Siker"), f"A HTML riportot elmentettem ide:\n{cel_utvonal}\n\nMegnyitás böngészőben...")
            webbrowser.open(f"file://{os.path.abspath(cel_utvonal)}")
        except Exception as e:
            messagebox.showerror(tr("Hiba"), tr(f"Nem sikerült létrehozni a HTML riportot:\n{e}"))

    def mappa_kotegelt_vizsgalat(self):
        mappa = filedialog.askdirectory(title="Válassza ki a dokumentumok mappáját")
        if not mappa:
            return

        self.utolso_mappa = Path(mappa)
        fajlok = sorted(p_ for p_ in self.utolso_mappa.iterdir()
                        if p_.is_file() and p_.suffix.lower() in TAMOGATOTT_KITERJESZTESEK)
        if len(fajlok) < 2:
            messagebox.showwarning(tr("Figyelem"), "A kiválasztott mappában legalább 2 db szöveg- vagy feliratfájl szükséges!")
            return

        for row in self.tree.get_children():
            self.tree.delete(row)

        hasznaljon_cache_ot = self.mappa_cache_var.get()
        hasznaljon_multiproc_ot = self.mappa_multiproc_var.get()

        self.statusz_var.set(tr("Kötegelt mappa elemzés háttérben fut..."))
        self._mozgasjelzo_inditasa(tr("Mappában lévő fájlpárok elemzése…"))
        self.update_idletasks()

        def mappa_hatter_szamolas():
            try:
                tartalmak = {}
                for fpath in fajlok:
                    try:
                        tartalmak[fpath.name] = olvas_szoveg_fajl(fpath)
                    except Exception:
                        pass

                fajl_nevek = list(tartalmak.keys())
                sorok_adat = []
                vizsgalt_parok = 0
                cache_talalatok = 0

                # Betöltjük a korábbi futtatásokból származó, fájltartalom-hash
                # alapú gyorsítótárat (ha a felhasználó bekapcsolta) - így egy
                # már korábban összehasonlított fájlpárt nem kell újraszámolni.
                cache = cache_betoltese() if hasznaljon_cache_ot else {}
                uj_parok = []  # (f1, t1, f2, t2, cache_kulcs) - amit tényleg ki kell számolni

                for i in range(len(fajl_nevek)):
                    for j in range(i + 1, len(fajl_nevek)):
                        f1, f2 = fajl_nevek[i], fajl_nevek[j]
                        t1, t2 = tartalmak[f1], tartalmak[f2]
                        kulcs = cache_kulcs(t1, t2) if hasznaljon_cache_ot else None

                        if hasznaljon_cache_ot and kulcs in cache:
                            win, tfidf, simhash = cache[kulcs]
                            sorok_adat.append((f1, f2, f"{win:.2f}%", f"{tfidf:.2f}%", f"{simhash:.2f}%"))
                            cache_talalatok += 1
                        else:
                            uj_parok.append((f1, t1, f2, t2, kulcs))
                        vizsgalt_parok += 1

                # A még ki nem számolt párokat egyszerre, párhuzamosan (ha
                # engedélyezve van) számoljuk ki, kihasználva a gép több
                # CPU-magját - ez nagy mappáknál jelentősen felgyorsítja a
                # kötegelt vizsgálatot a korábbi, egyszálas megoldáshoz képest.
                if uj_parok:
                    self.after(0, lambda: self.statusz_var.set(
                        f"Számítás: {len(uj_parok)} új fájlpár ({cache_talalatok} találat a gyorsítótárban)..."))

                    worker_bemenetek = [(f1, t1, f2, t2) for (f1, t1, f2, t2, _) in uj_parok]

                    if hasznaljon_multiproc_ot and len(uj_parok) > 1:
                        max_worker = min(os.cpu_count() or 2, len(uj_parok))
                        with concurrent.futures.ProcessPoolExecutor(max_workers=max_worker) as executor:
                            eredmenyek = list(executor.map(_parvizsgalat_worker, worker_bemenetek))
                    else:
                        eredmenyek = [_parvizsgalat_worker(b) for b in worker_bemenetek]

                    for (f1, t1, f2, t2, kulcs), (_, _, win, tfidf, simhash) in zip(uj_parok, eredmenyek):
                        sorok_adat.append((f1, f2, f"{win:.2f}%", f"{tfidf:.2f}%", f"{simhash:.2f}%"))
                        if hasznaljon_cache_ot and kulcs is not None:
                            cache[kulcs] = (win, tfidf, simhash)

                if hasznaljon_cache_ot:
                    cache_mentese(cache)

                self.after(0, lambda: self._frissit_mappa_tree_eredmeny(sorok_adat, vizsgalt_parok, cache_talalatok))
            except Exception as e:
                self.after(0, lambda hiba=e: messagebox.showerror(tr("Hiba"), str(hiba)))
            finally:
                self.after(0, self._mozgasjelzo_leallitasa)

        threading.Thread(target=mappa_hatter_szamolas, daemon=True).start()

    def _frissit_mappa_tree_eredmeny(self, sorok_adat, parok_szama, cache_talalatok=0):
        for adat in sorok_adat:
            self.tree.insert("", "end", values=adat)
        cache_info = f" (Ebből gyorsítótárból: {cache_talalatok} db)" if cache_talalatok else ""
        self.statusz_var.set(tr(f"Kötegelt vizsgálat kész. Összehasonlított fájlpárok: {parok_szama} db.{cache_info}"))
        self.notebook.select(self.ful_mappa)

    def _mappa_elem_duplakatt(self, event):
        kijelolt_item = self.tree.selection()
        if not kijelolt_item or not self.utolso_mappa:
            return

        ertekek = self.tree.item(kijelolt_item, "values")
        if not ertekek:
            return

        fajl1_nev, fajl2_nev = ertekek[0], ertekek[1]
        fajl1_utv = self.utolso_mappa / fajl1_nev
        fajl2_utv = self.utolso_mappa / fajl2_nev

        try:
            t1 = olvas_szoveg_fajl(fajl1_utv)
            self._allapot_mentes()
            self.fajl1_utvonal = str(fajl1_utv)
            self.text1.delete("1.0", "end")
            self.text1.insert("1.0", t1)
            self.cimke1_var.set(tr(f"Bal fájl: {fajl1_nev}"))
        except Exception as e:
            messagebox.showerror(tr("Hiba"), f"Nem sikerült megnyitni: {fajl1_nev}\n{e}")
            return

        try:
            t2 = olvas_szoveg_fajl(fajl2_utv)
            self.fajl2_utvonal = str(fajl2_utv)
            self.text2.delete("1.0", "end")
            self.text2.insert("1.0", t2)
            self.cimke2_var.set(tr(f"Jobb fájl: {fajl2_nev}"))
        except Exception as e:
            messagebox.showerror(tr("Hiba"), f"Nem sikerült megnyitni: {fajl2_nev}\n{e}")
            return

        self.notebook.select(self.ful_ketfajl)
        # NINCS automatikus self.osszehasonlitas() hívás!
        self.statusz_var.set(tr(f"Fájlok betöltve: {fajl1_nev} <-> {fajl2_nev}. Az elemzéshez kattints az 'Indítás' gombra!"))


if __name__ == "__main__":
    app = SzTextCompar()
    app.mainloop()
