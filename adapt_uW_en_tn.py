#!/usr/bin/env -S uv run
# -\*- coding: utf-8 -\*-
# SPDX-FileCopyrightText: © 2026 Robert Hunt <Freely.Given.org+OBD@gmail.com>
# SPDX-License-Identifier: CC0-1.0
#
# adapt_uW_en_tn.py
#
# Script to adapt the unfoldingWord® Translation Notes (en_tn) to suit the OET-RV
#
# Copyright (C) 2026 Robert Hunt
# Author: Robert Hunt <Freely.Given.org+OBD@gmail.com>
# License: CC0-1.0 (the script itself)
#   The adapted notes remain CC BY-SA 4.0 (see ADAPTATION_NOTICE.md)
#
"""
Adapt the unfoldingWord® Translation Notes (the en_tn repo, cloned into the parent folder)
    to imitate how the OET Readers' Version (OET-RV) handles names and some wording.

Steps:
    1/ Delete and freshly re-copy the tn_*.tsv files (and the manifest, etc.) from the parent folder.
    2/ In the Note column only, add the OET-RV name (from OET-RV_names_table.tsv) after the traditional name
        on its first use in each note (and again after EXPLAIN_WINDOW lines of a long note),
        e.g., 'Samuel' -> 'Samuel/Shmuel' then just 'Samuel', because the notes refer to the names in the ULT/UST.
        Link targets (e.g., '](../01/01.md)' and 'rc://…' support references) and the original-language Quote column aren't changed,
        nor are Bible book names in references like 'John 1:19', or text quoted from other Bible versions, e.g., '“…” (NIV)'.
    3/ Write ADAPTATION_NOTICE.md (required by CC BY-SA) and adaptation_log.tsv.

The names code block is shared (by copying) with adaptTyndaleResources.py, adaptUBSResources.py, and adaptSILOpenTranslatorsNotes.py
    so that this script is independent.

CHANGELOG:
    2026-11-19 First version
    2026-11-20 Keep the uW name and add the OET-RV name after it, e.g., 'Samuel (Shmuel)';
                and likewise for terms, e.g., 'the LORD (Yahweh)'; leave text quoted from other Bible versions unchanged
    2026-11-22 Update the shared OET-RV names code block for the names table changes (rows repeated for each OT/NT/DC segment, 'Explained' Y flag became 'CanonicalExplanation')
    2026-11-22 Explain names with the OET-RV names table 'NotesExplanation' (not the Greek forms used in the OET-RV ESFM files), and use a slash rather than parentheses, e.g., 'Shmuel/Samuel' or 'Samuel/Shmuel'; treat a slashed source alternative like a parenthesised one, e.g., 'Xerxes/Ahasuerus'; don't change names inside a replaced source explanation, e.g., 'Ahasuerus (Xerxes)'
    2026-11-26 Correct known errors in the source files (SOURCE_CORRECTIONS), and fail on stray backslashes (which make OpenBibleData fail)
"""
from collections import Counter, defaultdict
from csv import DictReader
from functools import lru_cache
import json
from pathlib import Path
import re
import shutil
import sys


LAST_MODIFIED_DATE = '2026-11-26' # by RJH
PROGRAM_NAME = "Adapt unfoldingWord Translation Notes for OET-RV"
PROGRAM_VERSION = '0.51'

THIS_FOLDER = Path(__file__).resolve().parent
SOURCE_FOLDER = THIS_FOLDER.parent # The original en_tn repo
COPIED_FILES = {'manifest.yaml':'manifest.yaml', 'media.yaml':'media.yaml', 'LICENSE.md':'uW_LICENSE.md', 'README.md':'uW_README.md'} # Source name: our name
OET_RV_FOLDER = Path('/srv/FreelyGiven/OpenEnglishTranslation--OET/translatedTexts/ReadersVersion/')
NAMES_TABLE_FILEPATH = OET_RV_FOLDER / 'OET-RV_names_table.tsv'

OWN_VERSIONS = {'ULT', 'UST', 'ULB', 'UDB'} # The notes refer to these (so quotes from them aren't protected like other versions)

EXPLAIN_WINDOW = 10 # Re-explain a name if it was last explained more than this many lines earlier (in the same note)
EXPLAIN_ONLY_FLAGGED_NAMES = False # True = only explain names with a CanonicalExplanation in the names table
MAX_TRADITIONAL_FRACTION = 0.2 # Don't change a name if the OET-RV text itself uses the traditional form more than this fraction of the time

# Traditional names that are also common English words or otherwise unsafe to change automatically
SKIP_NAMES = { 'Abed', 'Agar', 'Bath', 'Beer', 'Behemoth', 'Carpus', 'Cherub', 'Clement', 'Col', 'Crates',
    'Destiny', 'Epicurean', 'Epicureans', 'Ether', 'Fortune', 'Gob', 'Leviathan', 'Macron', 'Manes',
    'Media', 'Mica', 'Mortar', 'Narcissus', 'Onus', 'Phoenix', 'Shamed', 'Stoic', 'Straight', 'Tidal', 'Weeks',
    'Hebrew', 'Hebrews', 'Greek', 'Greeks', 'Aramaic', 'Latin', # Mostly refer to languages (or a book) in these resources
    'Corinthians', 'Ephesians', 'Philippians', 'Thessalonians', 'Colossians', 'Galatians', 'Romans', # Mostly refer to NT books
    'Josephus', # The historian
    'Nazarene', 'Judea', # Table maps these to Nazaret and Yehudah, which don't suit NT commentary
    }

# Terminology changes: (enabled, regex, replacement, description)
#   Because these notes refer to the ULT/UST, their term is kept, with ours added after it on first use, e.g., 'the LORD (Yahweh)'.
TERMINOLOGY_RULES = [
    (True, r'\b(?:[Tt]he )?LORD\b', 'Yahweh', "LORD → Yahweh"),
    # Disabled because the names code already gives 'John (Yohan) the Baptist' in these notes
    (False, r'\bJohn the Baptist\b', 'John the immerser', "John the Baptist → John the immerser"),
    # Disabled: OET-RV wording, but these notes discuss how to translate the terms themselves
    (False, r'\bSabbath\b', 'Rest Day', "Sabbath → Rest Day"),
    (False, r'\bsynagogue\b', 'meeting hall', "synagogue → meeting hall"),
    ]

PROTECTED_RE = re.compile(r'\]\([^)]*\)|\[\[rc://[^\]]*\]\]|rc://\S+|https?://\S+') # Link targets and support references
NOTE_COLUMN, NUM_COLUMNS = 6, 7 # Reference	ID	Tags	SupportReference	Quote	Occurrence	Note

############################################################################################################
# BEGIN OET-RV names code
#   This block is copied (identically) into adaptTyndaleResources.py, adaptUBSResources.py, adapt_uW_en_tn.py,
#       and adaptSILOpenTranslatorsNotes.py so that each repo's script is independent. Please keep the copies in sync.
#   The including script must first define OET_RV_FOLDER, NAMES_TABLE_FILEPATH, EXPLAIN_WINDOW, EXPLAIN_ONLY_FLAGGED_NAMES,
#       MAX_TRADITIONAL_FRACTION, SKIP_NAMES, and TERMINOLOGY_RULES (a list of (enabled, regex, replacement, description)
#       which is used unless the NameAdapter is given its own compiled terminology rules).
############################################################################################################

POSSESSIVE_RE = re.compile(r"(?:[’']s\b|[’'](?= [a-z]))") # ’s or (after s) a bare ’ followed by a lower-case word
BOOK_REFERENCE_AFTER_RE = re.compile(r'\s\d{1,3}(?=[:.,;–\-)\]\s]|$)') # e.g., the ' 1' in 'John 1:19' (the name is a Bible book)
BOOK_NUMBER_BEFORE_RE = re.compile(r'(?:^|\W)[1-4]\s$') # e.g., the '1 ' in '1 John'
ALTERNATIVE_NAME_RE = re.compile(r" \(([\w’' -]+)\)|/([A-Z][\w’'-]*)") # e.g., the ' (Xerxes)' in 'Ahasuerus (Xerxes)' or the '/Ahasuerus' in 'Xerxes/Ahasuerus'
NUMBERED_BOOK_NAMES = {'Samuel', 'John', 'Peter', 'Esdras', 'Ezra'} # Names that are also numbered Bible books, e.g., '2 Samuel'

# Text quoted from (or attributed to) these Bible versions is never changed, e.g., '“For God so loved…” (NIV)'
#   (except for a resource's own base translation(s) — see NameAdapter ownVersions)
BIBLE_VERSIONS = ('KJV', 'AV', 'NKJV', 'NIV', 'NIV84', 'NIV93', 'NIV11', 'NIV2011', 'TNIV', 'NIrV', 'NIRV',
    'NLT', 'NLT96', 'NLT04', 'NLV', 'RSV', 'NRSV', 'NRSVue', 'ESV', 'NASB', 'NASB95', 'NASB20', 'NAB', 'NABRE',
    'JB', 'NJB', 'NEB', 'REB', 'GNT', 'GNB', 'TEV', 'CEV', 'NCV', 'NET', 'HCSB', 'CSB', 'CEB', 'BSB', 'BLB', 'MSB',
    'ASV', 'JPS', 'NJPS', 'NJPSV', 'TLB', 'LB', 'ULT', 'UST', 'ULB', 'UDB', 'GW', 'ERV', 'ICB', 'MSG', 'AMP',
    'LEB', 'WEB', 'YLT', 'DRA', 'LXX', 'JBP', 'Phps', 'Phillips', 'Mft', 'Moffatt', 'Knox', 'Weymouth', 'Goodspeed',
    'TRT', 'EASY', 'T4T', 'VOICE', 'Voice', 'TLV', 'CJB', 'AT', 'BE', 'TNT', 'TOB', 'NOB', 'NVSR', 'SSA',
    'GECL', 'ITCL', 'FRCL', 'SPCL', 'DUCL', 'BRCL', 'Vulgate', 'Syriac', 'Peshitta', 'Targum')
MAX_QUOTE_LENGTH = 800 # characters
INLINE_TAG_RE = re.compile(r'</?(?:a|b|i|u|s|l|em|strong|span|sup|sub|small|cite)\b[^>]*>') # Other tags separate blocks of text
_VERSION_PATTERN = '|'.join(re.escape(version) for version in sorted(BIBLE_VERSIONS, key=len, reverse=True)) \
                    + r'|[A-Z][\w-]+(?: [A-Z][\w-]+)* [Bb]ack [Tt]ranslation' # e.g., '(Kankanaey Back Translation)'
VERSION_RE = re.compile(rf'(?<![\w-])(?:{_VERSION_PATTERN})(?![\w-])')
# These patterns are used on 'masked' text, where inline tags are replaced by \x00 and other tags by \x01
_IG = r'[\s\x00]*' # Ignorable whitespace and inline tags
_VERSION_LIST = rf'(?<![\w-])(?:{_VERSION_PATTERN})(?![\w-])(?:{_IG}(?:,|/|;|&|and|or){_IG}(?<![\w-])(?:{_VERSION_PATTERN})(?![\w-]))*' \
                rf'(?:{_IG}(?:footnote|margin|text|note|\d{{2,4}}))?'
_ATTRIBUTION = rf'[(\[]{_IG}(?:[^()\[\]\x01]{{0,40}}?[\s\x00,;:])?{_VERSION_LIST}(?:{_IG}[,;][^()\[\]\x01]{{0,60}})?[\s\x00,;.]*[)\]]'
    # e.g., '(NIV)', '(John 3:16, NIV)', '(RSV; Greek skēnē)'
_REFERENCE = r'(?:[1-4] ?)?[A-Z][a-z]{1,14}\.? \d{1,3}(?:[:.]\d{1,3}(?:[–-]\d{1,3})?)?' # e.g., 'Jn 3:16'
_QUOTE = r'(?:“[^“”\x01]{1,800}”|‘[^‘\x01]{1,800}?’(?!\w)|"[^"\x01]{1,800}")'
QUOTE_THEN_VERSION_RES = ( # Each has a closing quote and an attribution
    re.compile(rf'(?P<close>[”’"]){_IG}[.,;:]?{_IG}(?:{_REFERENCE}{_IG})?(?P<attribution>{_ATTRIBUTION})'), # '“…” (NIV)'
    re.compile(rf'(?P<close>[”’"]){_IG}[;,]{_IG}(?P<attribution>{_VERSION_LIST})(?={_IG}[)\]])'), # '(“tent”; RSV)'
    re.compile(rf'(?P<close>[”’"]){_IG}[.,]?{_IG}(?:in|from|according to){_IG}(?:the{_IG})?(?P<attribution>{_VERSION_LIST})'), # '“boxwood” in NEB'
    )
_BETWEEN = r'[^“”‘"\x01.!?;]{0,80}?' # Not crossing a sentence end or another quote
VERSION_THEN_QUOTE_RE = re.compile(rf'(?P<attribution>{_VERSION_LIST}){_IG}(?:’s)?' # e.g., 'NIV: “…”', 'the RSV has “…”', 'NJB (similarly JB), “…”'
    rf'(?:{_BETWEEN}(?<![\w-])(?:has|have|had|reads?|translates?|translated|translation|renders?|rendered|rendering|says|said|gives|gave|uses|used|puts? it'
                    rf'|offers|prefers|provides|model|calls?|called|with|as)(?![\w-]){_BETWEEN}(?::|,)?|{_BETWEEN}[:,])?{_IG}'
    rf'(?P<quote>{_QUOTE})')
GENERIC_VERSIONS_THEN_QUOTE_RE = re.compile(rf'(?<![\w-])(?:translations|versions)(?![\w-]){_BETWEEN}(?<![\w-])(?:have|has|read|reads|say|says|translate|translates|render|renders)(?![\w-])'
                                            rf'{_BETWEEN}(?::|,)?{_IG}(?P<quote>{_QUOTE})') # e.g., 'many modern translations have: “…”'
VERSION_NAME_RE = re.compile(r"\b(?:King James|(?:New )?Jerusalem Bible|Matthew[’']s Bible)\b") # Names that contain a person or place name
BLOCKQUOTE_RE = re.compile(r'<blockquote\b[^>]*>(.*?)</blockquote>', re.DOTALL)
SIMPLE_LIST_ITEM_RE = re.compile(r'<li\b[^>]*>(<p\b[^>]*>(?:(?!</?(?:p|li|ul|ol|blockquote)\b).)*</p>)</li>', re.DOTALL)
TABLE_CELL_RE = re.compile(r'<td\b[^>]*>(.*?)</td>', re.DOTALL)
ATTRIBUTION_RE = re.compile(rf'(?P<attribution>{_ATTRIBUTION})')
VERSION_INTRODUCTION_RE = re.compile(rf'(?P<attribution>{_VERSION_LIST})[^.!?\x01]{{0,60}}:[\s\x00\x01]*$') # e.g., '…the RSV says:</p>' (before a blockquote)
ATTRIBUTED_BLOCK_END_RE = re.compile(rf'(?P<attribution>{_ATTRIBUTION}(?:{_IG}{_ATTRIBUTION})*)[\s\x00\x01]*$') # e.g., '…Jerusalem (GW)</p>'
OPENING_QUOTES = {'”':'“', '’':'‘', '"':'"'}
PROTECT_START, PROTECT_END = '\uE000', '\uE001' # Private-use characters for our placeholders
_protectionCount = 0 # Gives each protectSpans call its own placeholders (so that protected text can be protected again)


def maskTags(text:str) -> str:
    """
    Return the text with each tag replaced by the same number of \\x00 (inline tags) or \\x01 (other tags) characters,
        so that our quote patterns can see the text (but not cross block boundaries) and the character positions don't change.
    """
    return re.sub(r'<[^>]*>', lambda m: ('\x00' if INLINE_TAG_RE.fullmatch(m.group(0)) else '\x01') * len(m.group(0)), text)
# end of maskTags


def versionQuoteSpans(text:str, ownVersions=frozenset()) -> list[tuple[int,int]]:
    """
    Find text quoted from other Bible versions (which we mustn't change), e.g.,
        '“For God so loved…” (NIV)', '“…” (Jn 3:16 NIV)', '“sanctuary”; <a>RSV</a>)', '“boxwood” in NEB',
        'NIV: “…”', 'the RSV has “…”', '<a>CEV</a> renders <s>…</s> as “…”', 'many modern translations have: “…”',
        (SIL) blockquotes like '<blockquote><p>Simon was coming into Jerusalem (GW)</p></blockquote>'
            or introduced by '…the RSV says:</p>', list items like '<li><p>…to Jesus (NJB)</p></li>', table cells like '<td><p>Don’t Be Ashamed of Jesus (NCV)</p></td>',
        and the names of versions like 'King James Version' and 'New Jerusalem Bible'.

    The text can contain (XML/HTML) tags. Quotes attributed only to ownVersions (the resource's own base translations)
        aren't included.

    Returns a sorted list of non-overlapping (start, end) character spans (including the attributions).
    """
    spans = [(match.start(), match.end()) for match in VERSION_NAME_RE.finditer(text)]
    if not VERSION_RE.search(text) and not GENERIC_VERSIONS_THEN_QUOTE_RE.search(text): return spans
    masked = maskTags(text)
    def isOtherVersion(attribution:str) -> bool:
        return bool(set(VERSION_RE.findall(attribution)) - set(ownVersions))
    for quoteThenVersionRE in QUOTE_THEN_VERSION_RES:
        for match in quoteThenVersionRE.finditer(masked):
            if not isOtherVersion(match.group('attribution')): continue
            closeIndex = match.start('close')
            lowIndex = max(masked.rfind('\x01', 0, closeIndex) + 1, closeIndex - MAX_QUOTE_LENGTH)
            openIndex = masked.rfind(OPENING_QUOTES[match.group('close')], lowIndex, closeIndex)
            if openIndex >= 0: spans.append((openIndex, match.end()))
    for match in VERSION_THEN_QUOTE_RE.finditer(masked):
        if isOtherVersion(match.group('attribution')): spans.append((match.start(), match.end()))
    for match in GENERIC_VERSIONS_THEN_QUOTE_RE.finditer(masked):
        spans.append((match.start('quote'), match.end('quote')))
    introducedEnd = None # End of the last blockquote that was introduced by a version, e.g., 'the RSV says:'
    for match in BLOCKQUOTE_RE.finditer(text):
        attributionMatch = ATTRIBUTED_BLOCK_END_RE.search(masked, match.start(1), match.end(1))
        if attributionMatch and isOtherVersion(attributionMatch.group('attribution')):
            spans.append((match.start(1), match.end(1)))
            continue
        before = masked[max(0, match.start()-300):match.start()].rstrip('\x01\x00 \n')
        if introducedEnd is not None and not masked[introducedEnd:match.start()].strip('\x01\x00 \n'): # Follows on from an introduced blockquote
            spans.append((match.start(1), match.end(1))); introducedEnd = match.end(); continue
        introductionMatch = VERSION_INTRODUCTION_RE.search(before[before.rfind('\x01')+1:])
        if introductionMatch and isOtherVersion(introductionMatch.group('attribution')):
            spans.append((match.start(1), match.end(1))); introducedEnd = match.end()
        else: introducedEnd = None
    for match in SIMPLE_LIST_ITEM_RE.finditer(text): # e.g., '<li><p>Then they took the colt to Jesus (NJB)</p></li>'
        attributionMatch = ATTRIBUTED_BLOCK_END_RE.search(masked, match.start(1), match.end(1))
        if attributionMatch and isOtherVersion(attributionMatch.group('attribution')):
            spans.append((match.start(1), match.end(1)))
    for match in TABLE_CELL_RE.finditer(text): # e.g., section headings from various versions '<td><p>Don’t Be Ashamed of Jesus (NCV)</p></td>'
        attributionEnds = [attributionMatch.end() for attributionMatch in ATTRIBUTION_RE.finditer(masked, match.start(1), match.end(1))
                                if isOtherVersion(attributionMatch.group('attribution'))]
        if attributionEnds: spans.append((match.start(1), attributionEnds[-1]))
    mergedSpans = []
    for start, end in sorted(spans):
        if mergedSpans and start <= mergedSpans[-1][1]:
            mergedSpans[-1] = (mergedSpans[-1][0], max(end, mergedSpans[-1][1]))
        else: mergedSpans.append((start, end))
    return mergedSpans
# end of versionQuoteSpans


def protectSpans(text:str, spans:list[tuple[int,int]]) -> tuple[str,list[str]]:
    """
    Replace the text (but not any tags) inside each span with numbered placeholders,
        so that later processing (which still sees all the tags) can't change it.

    Returns the new text and the list of saved pieces (for restoreSpans).
    """
    global _protectionCount
    if not spans: return text, []
    _protectionCount += 1
    pieces, saved, lastEnd = [], [f'{_protectionCount}:'], 0 # saved[0] is our placeholder prefix
    for start, end in spans:
        pieces.append(text[lastEnd:start])
        for piece in re.split(r'(<[^>]*>)', text[start:end]):
            if piece.startswith('<') or not piece: pieces.append(piece)
            else:
                pieces.append(f'{PROTECT_START}{saved[0]}{len(saved)}{PROTECT_END}')
                saved.append(piece)
        lastEnd = end
    pieces.append(text[lastEnd:])
    return ''.join(pieces), saved
# end of protectSpans


def restoreSpans(text:str, saved:list[str]) -> str:
    if not saved: return text
    placeholderRE = re.compile(f'{PROTECT_START}{saved[0]}(\\d+){PROTECT_END}')
    text, numRestored = placeholderRE.subn(lambda m: saved[int(m.group(1))], text)
    assert numRestored == len(saved) - 1, f"Only restored {numRestored} of {len(saved)-1} protected pieces"
    return text
# end of restoreSpans


def countEsfmWords() -> Counter:
    """
    Count how often each capitalised word (or hyphenated word) is used in the OET-RV text
        (outside of name explanations like 'Yeshua \\add !(Jesus)\\add*'),
        so we can tell if the OET-RV actually keeps a traditional name.

    Returns a counter of words used in the OET-RV text.
    """
    wordCounts = Counter()
    explanationRE = re.compile(r"([A-Z][\w’'-]*)(?:\\\+?add\*)? \\\+?add !\(([^)]+)\)")
    for filepath in sorted(OET_RV_FOLDER.glob('OET-RV_*.ESFM')):
        text = re.sub(r'¦\d+', '', filepath.read_text(encoding='utf-8'))
        # Now count words in the Bible text only (not in introductions, headings, comments, or footnotes)
        text = '\n'.join(line for line in text.splitlines()
                            if not re.match(r'\\(rem|i[a-z]*|li\d?|mt\d?|toc\d|h|id|usfm|ide|s\d?|r|d|ms\d?|mr|sr|cl)\b', line))
        text = re.sub(r'\\f .+?\\f\*|\\x .+?\\x\*', ' ', text) # Remove footnotes and cross-references
        text = explanationRE.sub(r'\1', text) # Remove explanations
        text = re.sub(r'\([^()]*\)', ' ', text) # Remove other parenthesised text (e.g., unmarked explanations)
        text = re.sub(r"[\w’']+/ ?([\w’']+)", r'\1', text) # Remove slashed explanations like Yakov/Jacob
        text = re.sub(r'\\[a-z0-9+]+\*?|[@&*≈~]', ' ', text).replace("'", '’') # Remove markers and OET-RV special characters
        wordCounts.update(re.findall(r"(?<![\w’'-])[A-Z][\w’']*(?:[- ][A-Z][\w’']*)*", text))
    print(f"  Counted {len(wordCounts):,} capitalised words in the OET-RV ESFM files")
    return wordCounts
# end of countEsfmWords


def loadNames(esfmWordCounts:Counter) -> dict[str,dict]:
    """
    Load the OET-RV names table and decide how to explain each name.

    Returns a dict with traditional names as keys.
    """
    rowsByTraditionalName = defaultdict(list)
    with open(NAMES_TABLE_FILEPATH, 'rt', encoding='utf-8', newline='') as tsvFile:
        for row in DictReader(tsvFile, delimiter='\t'):
            rowsByTraditionalName[row['TraditionalName'].strip()].append(row)

    @lru_cache(maxsize=None)
    def esfmCount(name:str) -> int:
        """ How often the OET-RV uses this name (including possessive and multi-word uses) """
        return sum(count for word,count in esfmWordCounts.items()
                    if word == name or word == f"{name}’s" or word.startswith(f'{name} ') or word.endswith(f' {name}'))

    names, skippedAmbiguous, skippedKept = {}, [], []
    for traditionalName, rows in rowsByTraditionalName.items():
        if not traditionalName or traditionalName in SKIP_NAMES \
        or '' in traditionalName.split('-'): # e.g., 'Beth-' name components
            continue
        rows = [row for row in rows if row['RVName'].strip() and row['RVName'].strip() != traditionalName
                    and '(0)' not in row['Comment']] # '(0)' entries are name components and titles
        if not rows: continue
        if len({row['RVName'] for row in rows}) > 1: # Same traditional name maps to different RV names
            flaggedRows = list({row['RVName'].strip():row for row in rows if (row['CanonicalExplanation'] or '').strip()}.values()) # Rows repeat for each OT/NT/DC segment
            if len(flaggedRows) != 1:
                skippedAmbiguous.append(f"{traditionalName}={'/'.join(dict.fromkeys(row['RVName'] for row in rows))}")
                continue
            rows = flaggedRows # Use the main (explained) one
        row = rows[0]
        rvName = row['RVName'].strip()
        traditionalCount = esfmCount(traditionalName)
        if traditionalCount > MAX_TRADITIONAL_FRACTION * (traditionalCount + esfmCount(rvName)):
            skippedKept.append(traditionalName) # The OET-RV text often still uses the traditional form
            continue
        isFlagged = bool( (row['CanonicalExplanation'] or '').strip() )
        if EXPLAIN_ONLY_FLAGGED_NAMES and not isFlagged:
            explanation = None
        else:
            explanation = (row['NotesExplanation'] or '').strip() or traditionalName # e.g., 'Ahasuerus/Xerxes'
        names[traditionalName] = {'rvName':rvName, 'explanation':explanation, 'flagged':isFlagged}
    print(f"  Loaded {len(names):,} names to change from {NAMES_TABLE_FILEPATH.name}")
    if skippedKept:
        print(f"  Skipped {len(skippedKept)} names still often used in OET-RV text: {', '.join(skippedKept)}")
    if skippedAmbiguous:
        print(f"  Skipped {len(skippedAmbiguous)} ambiguous names: {', '.join(skippedAmbiguous)}")
    return names
# end of loadNames


def makeNamesRegex(names:dict[str,dict]) -> re.Pattern:
    """
    Make one big regex that matches any of the traditional names (longest first).

    Parts after a hyphen can be either case, e.g., 'Abel-meholah' also matches 'Abel-Meholah'.
    """
    def namePattern(name:str) -> str:
        parts = name.split('-')
        return '-'.join([re.escape(parts[0])] + [f'[{p[0].upper()}{p[0].lower()}]{re.escape(p[1:])}' for p in parts[1:]])
    alternatives = '|'.join(namePattern(name) for name in sorted(names, key=len, reverse=True))
    return re.compile(rf"(?<![\w’'-])({alternatives})(?![\w]|-\w)")
# end of makeNamesRegex


def possessive(name:str) -> str:
    """ Jesus -> Jesus’, John -> John’s """
    return name + ('’' if name.endswith('s') else '’s')
# end of possessive


def matchCase(replacement:str, matchedText:str) -> str:
    if replacement.startswith('<') or not matchedText or not replacement: return replacement
    if matchedText[0].isupper(): return replacement[0].upper() + replacement[1:]
    return replacement
# end of matchCase


class NameAdapter:
    """
    Changes names (and some terminology) in text fields,
        explaining each name on its first use in an item (entry/note/article),
        and again if it hasn't been explained within the last EXPLAIN_WINDOW fields/lines.

    By default (for dictionaries and articles), names are changed to the OET-RV names,
        e.g., 'Samuel' -> 'Shmuel/Samuel' then just 'Shmuel'.
    If theirNameFirst is set (for notes that refer to their own translation, e.g., the NLT, ULT, or BSB),
        their name is kept, with the OET-RV name after it on first use, e.g., 'Samuel/Shmuel' then just 'Samuel',
        and likewise (but in parentheses) for their terms, e.g., 'the LORD (Yahweh)'.

    Text quoted from other Bible versions (not ownVersions) can be left unchanged using adaptProtected().
    """
    def __init__(self, names:dict[str,dict], namesRE:re.Pattern, counts:Counter, *,
                    theirNameFirst:bool=False, ownVersions=frozenset(), terminologyRules:list|None=None) -> None:
        self.names, self.namesRE, self.counts = names, namesRE, counts
        self.theirNameFirst, self.ownVersions = theirNameFirst, frozenset(ownVersions)
        self.lowerNames = {name.lower():name for name in names}
        self.terminologyRules = terminologyRules if terminologyRules is not None \
                                    else [(re.compile(regex), replacement, description)
                                            for enabled, regex, replacement, description in TERMINOLOGY_RULES if enabled]
        self.lastExplainedLine:dict[str,int] = {}
        self.lineNumber = 0

    def newItem(self) -> None:
        self.lastExplainedLine = {}

    def adaptProtected(self, text:str, adaptFunction) -> str:
        """
        Call adaptFunction(text) but with any text quoted from other Bible versions protected from changes.
        """
        spans = versionQuoteSpans(text, self.ownVersions)
        if not spans: return adaptFunction(text)
        self.counts['KEEP\tQuote from another Bible version (unchanged)'] += len(spans)
        protectedText, saved = protectSpans(text, spans)
        return restoreSpans(adaptFunction(protectedText), saved)

    def adaptText(self, text:str) -> str:
        """
        Adapt one plain-text field (counted as one 'line' for the explanation window).
        """
        self.lineNumber += 1
        return self.adaptProtected(text, lambda t: self.adaptNames(self.adaptTerminology(t, self.terminologyRules)))

    def adaptTerminology(self, text:str, rules:list) -> str:
        for regex, replacement, description in rules:
            if self.theirNameFirst: text = self.explainTerms(text, regex, replacement, description)
            else:
                text, numChanges = regex.subn(lambda m: matchCase(m.expand(replacement), m.group(0)), text)
                if numChanges: self.counts[f'TERM\t{description}'] += numChanges
        return text

    def explainTerms(self, text:str, regex:re.Pattern, replacement:str, description:str) -> str:
        """
        For notes that refer to their own translation: keep their term, but add ours after it on first use
            (and again after EXPLAIN_WINDOW lines), e.g., 'the LORD (Yahweh)', 'the LORD’s (Yahweh’s)'.
        """
        result, lastEnd = [], 0
        for match in regex.finditer(text):
            ourTerm = re.sub(r'<[^>]*>', '', matchCase(match.expand(replacement), match.group(0))).strip().rstrip('.,;:!?')
            key = f'TERM:{ourTerm}'
            if not ourTerm or self.lineNumber - self.lastExplainedLine.get(key, -9999) <= EXPLAIN_WINDOW: continue
            self.lastExplainedLine[key] = self.lineNumber
            self.counts[f'TERM\t{description} (added after their term)'] += 1
            theirTerm, endIndex, trailing = match.group(0), match.end(), ''
            if (punctuationMatch := re.search(r'([.,;:!?]+)(</\w+>)$', theirTerm)): # e.g., '<span class="divine-name">Lord,</span>'
                theirTerm, trailing = theirTerm[:punctuationMatch.start()] + punctuationMatch.group(2), punctuationMatch.group(1)
            elif (possessiveMatch := re.match(r"[’']s\b", text[endIndex:])): # e.g., 'the LORD’s (Yahweh’s)'
                theirTerm, endIndex, ourTerm = theirTerm + possessiveMatch.group(0), endIndex + len(possessiveMatch.group(0)), possessive(ourTerm)
            result.append(text[lastEnd:match.start()])
            result.append(f'{theirTerm} ({ourTerm}){trailing}')
            lastEnd = endIndex
        result.append(text[lastEnd:])
        return ''.join(result)

    def adaptNames(self, text:str) -> str:
        result, lastEnd = [], 0
        for match in self.namesRE.finditer(text):
            if match.start() < lastEnd: continue # Inside text that we already replaced, e.g., the 'Xerxes' in 'Ahasuerus (Xerxes)'
            matchedName = match.group(1)
            traditionalName = matchedName if matchedName in self.names else self.lowerNames.get(matchedName.lower())
            if traditionalName is None or not matchedName[0].isupper(): continue
            if BOOK_REFERENCE_AFTER_RE.match(text, match.end()) \
            or (traditionalName in NUMBERED_BOOK_NAMES and BOOK_NUMBER_BEFORE_RE.search(text[:match.start()])):
                continue # It's a Bible book name in a reference, e.g., 'John 1:19' or '1 John'
            info = self.names[traditionalName]
            rvName = info['rvName']
            # Possessives: ’s, or a bare ’ after a name ending in 's' (but not a closing quote)
            possessiveMatch = POSSESSIVE_RE.match(text, match.end())
            if possessiveMatch and len(possessiveMatch.group(0)) == 1 \
            and (not matchedName.endswith('s') or text[max(0,match.start()-1):match.start()] in ('‘',"'")):
                possessiveMatch = None # Not a possessive, e.g., ‘Jesus’ is (a closing quote)
            endIndex = nameEndIndex = possessiveMatch.end() if possessiveMatch else match.end()
            # See if the source already follows the name with a parenthesised (or slashed) alternative that we'd change to the same RV name
            alreadyExplainedMatch, alternativeName = ALTERNATIVE_NAME_RE.match(text, endIndex), None
            if alreadyExplainedMatch:
                alternative = alreadyExplainedMatch.group(1) or alreadyExplainedMatch.group(2)
                if alternative == rvName: # e.g., 'Syria (Aram)'
                    endIndex = alreadyExplainedMatch.end()
                elif alternative != traditionalName and self.names.get(alternative, {}).get('rvName') == rvName: # e.g., 'Ahasuerus (Xerxes)'
                    endIndex, alternativeName = alreadyExplainedMatch.end(), alternative
                else: alreadyExplainedMatch = None
            needsExplanation = info['explanation'] is not None \
                and (alreadyExplainedMatch or self.lineNumber - self.lastExplainedLine.get(rvName, -9999) > EXPLAIN_WINDOW)
            ourName = rvName + ('’s' if possessiveMatch else '') # OET-RV uses 'Paulos's' (not 'Paulos'')
            if self.theirNameFirst: # Keep their name, adding ours on first use, e.g., 'Samuel/Shmuel'
                if not needsExplanation: continue # Leave their name unchanged
                self.lastExplainedLine[rvName] = self.lineNumber
                if alreadyExplainedMatch and not alternativeName: continue # They already give our name, e.g., 'Syria (Aram)'
                self.counts[f"NAME\t{traditionalName} → {traditionalName}/{rvName}"] += 1
                # e.g., 'Samuel’s' -> 'Samuel’s/Shmuel’s', 'Ahasuerus (Xerxes)' -> 'Ahasuerus/Ahashverosh (Xerxes)',
                #   or 'Xerxes/Ahasuerus' -> 'Xerxes/Ahasuerus/Ahashverosh'
                if alternativeName and alreadyExplainedMatch.group(2): rvText = f'{text[match.start():endIndex]}/{ourName}'
                else: rvText = f'{text[match.start():nameEndIndex]}/{ourName}{text[nameEndIndex:endIndex]}'
            else: # Change to our name, explaining it on first use, e.g., 'Shmuel/Samuel'
                self.counts[f"NAME\t{traditionalName} → {rvName}"] += 1
                rvText = ourName
                if needsExplanation:
                    self.lastExplainedLine[rvName] = self.lineNumber
                    explanation = info['explanation']
                    if alternativeName and alternativeName not in explanation.split('/'): # e.g., 'Ahashverosh/Ahasuerus/Xerxes'
                        explanation = explanation.replace(traditionalName, f'{traditionalName}/{alternativeName}', 1)
                    if possessiveMatch: # e.g., 'Yeshua’s/Jesus’'
                        explanation = '/'.join(possessive(part) for part in explanation.split('/'))
                    rvText = f'{rvText}/{explanation}'
            result.append(text[lastEnd:match.start()])
            result.append(rvText)
            lastEnd = endIndex
        result.append(text[lastEnd:])
        return ''.join(result)
    # end of NameAdapter.adaptNames
# end of NameAdapter class

############################################################################################################
# END OET-RV names code
############################################################################################################

# Errors in the original unfoldingWord files: (filepath, wrong text, correct text, description)
SOURCE_CORRECTIONS = [
    ('tn_JER.tsv', '(../05/11\\\\.md)', '(../05/11.md)', "a broken link to Jeremiah 5:11 (with stray backslashes) in a 5:15 note was fixed"),
    ]
ALLOWED_BACKSLASH_RE = re.compile(r'\\n') # The TSV notes use \n for line breaks
KNOWN_STRAY_BACKSLASHES = {}

############################################################################################################
# BEGIN stray backslash check code
#   This block is copied (identically) into adaptTyndaleResources.py, adaptUBSResources.py, adapt_uW_en_tn.py,
#       and adaptSILOpenTranslatorsNotes.py so that each repo's script is independent. Please keep the copies in sync.
#   The including script must first define THIS_FOLDER, SOURCE_CORRECTIONS, ALLOWED_BACKSLASH_RE, and KNOWN_STRAY_BACKSLASHES.
#   OpenBibleData fails on stray backslashes (e.g., left-over or mistyped USFM-style markers) in the text that it displays,
#       so we find them here (where the file and line are known) rather than partway through a long OBD build.
CHECKED_SUFFIXES = {'.json', '.xml', '.html', '.htm', '.tsv', '.txt', '.md'}


def applySourceCorrections(counts:Counter) -> None:
    """
    Correct known errors in the freshly copied source files (before they're adapted).

    SOURCE_CORRECTIONS entries are (filepath relative to THIS_FOLDER, wrong text, correct text, description).
    Each wrong text must occur exactly once (so that it's not changed somewhere unexpected),
        but it's only noted if it's not found (because it might have been fixed in the source).
    """
    for relativePath, wrongText, correctText, description in SOURCE_CORRECTIONS:
        filepath = THIS_FOLDER / relativePath
        text = filepath.read_text(encoding='utf-8')
        numFound = text.count(wrongText)
        if numFound == 0:
            print(f"  NOTE: Source correction no longer needed (fixed in the source?): {relativePath} {wrongText!r}")
            continue
        if numFound > 1:
            sys.exit(f"ERROR: Source correction {wrongText!r} found {numFound} times in {relativePath} (expected once)")
        filepath.write_text(text.replace(wrongText, correctText), encoding='utf-8')
        counts[f'CORRECTION\t{description}'] += 1
        print(f"  Corrected {relativePath}: {description}")
# end of applySourceCorrections


def sourceCorrectionsNotice() -> str:
    """
    Return the ADAPTATION_NOTICE.md section listing SOURCE_CORRECTIONS (or '' if there are none).
    """
    if not SOURCE_CORRECTIONS: return ''
    return "\n## Corrections\n\nThese errors in the original files were also corrected:\n\n" \
            + ''.join(f"- `{relativePath}`: {description}\n" for relativePath, _wrong, _correct, description in SOURCE_CORRECTIONS)
# end of sourceCorrectionsNotice


def _jsonStrings(value):
    if isinstance(value, dict):
        for subValue in value.values(): yield from _jsonStrings(subValue)
    elif isinstance(value, list):
        for item in value: yield from _jsonStrings(item)
    elif isinstance(value, str): yield value
# end of _jsonStrings


def checkStrayBackslashes(filepaths:list[Path]) -> None:
    """
    Exit with a list of them all if any adapted text file contains a backslash
        that isn't allowed by ALLOWED_BACKSLASH_RE (e.g., USFM-style \\heb…\\heb* markers)
        or listed (with its surrounding text) in KNOWN_STRAY_BACKSLASHES.

    JSON files are checked after decoding (so JSON escapes like \\" don't count).
    """
    strays, unusedKnown = [], {(relativePath, snippet) for relativePath, snippets in KNOWN_STRAY_BACKSLASHES.items() for snippet in snippets}
    numChecked = 0
    for filepath in filepaths:
        if filepath.suffix.lower() not in CHECKED_SUFFIXES: continue
        relativePath = str(filepath.relative_to(THIS_FOLDER))
        fileText = filepath.read_text(encoding='utf-8')
        numChecked += 1
        if '\\' not in fileText: continue
        isJSON = filepath.suffix.lower() == '.json'
        for text in (_jsonStrings(json.loads(fileText)) if isJSON else (fileText,)):
            if '\\' not in text: continue
            allowed = set()
            if ALLOWED_BACKSLASH_RE is not None:
                for match in ALLOWED_BACKSLASH_RE.finditer(text): allowed.update(range(match.start(), match.end()))
            for snippet in KNOWN_STRAY_BACKSLASHES.get(relativePath, ()):
                for match in re.finditer(re.escape(snippet), text):
                    allowed.update(range(match.start(), match.end()))
                    unusedKnown.discard((relativePath, snippet))
            for match in re.finditer(r'\\', text):
                if match.start() not in allowed:
                    where = 'in a JSON string' if isJSON else f'line {text.count(chr(10), 0, match.start())+1:,}'
                    context = text[max(0, match.start()-50):match.end()+30].replace('\n', ' ')
                    strays.append(f"{relativePath} {where}: …{context}…")
    for relativePath, snippet in sorted(unusedKnown):
        print(f"  NOTE: Known stray backslash no longer found (fixed in the source?): {relativePath} {snippet!r}")
    if strays:
        print(f"\nFound {len(strays):,} stray backslash{'' if len(strays)==1 else 'es'} (which would make OpenBibleData fail):")
        for stray in strays[:50]: print(f"  {stray}")
        if len(strays) > 50: print(f"  …and {len(strays)-50:,} more")
        sys.exit("ERROR: Add a SOURCE_CORRECTIONS entry for each error (and report it to the source),"
                 " or add it to ALLOWED_BACKSLASH_RE or KNOWN_STRAY_BACKSLASHES if it's intended or unused.")
    print(f"  Checked {numChecked:,} files for stray backslashes")
# end of checkStrayBackslashes

# END stray backslash check code
############################################################################################################


def copySourceFiles() -> list[Path]:
    """
    Delete any previous copies and re-copy the source files.

    Returns the list of copied TSV files.
    """
    for oldPath in THIS_FOLDER.glob('tn_*.tsv'): oldPath.unlink()
    tsvPaths = []
    for sourcePath in sorted(SOURCE_FOLDER.glob('tn_*.tsv')):
        destinationPath = THIS_FOLDER / sourcePath.name
        shutil.copy2(sourcePath, destinationPath)
        tsvPaths.append(destinationPath)
    for sourceName, destinationName in COPIED_FILES.items():
        shutil.copy2(SOURCE_FOLDER / sourceName, THIS_FOLDER / destinationName)
    if not tsvPaths:
        sys.exit(f"ERROR: No tn_*.tsv files found in '{SOURCE_FOLDER}'")
    print(f"  Copied {len(tsvPaths)} TSV files from '{SOURCE_FOLDER}'")
    return tsvPaths
# end of copySourceFiles


def adaptNoteLine(line:str, adapter:NameAdapter) -> str:
    """
    Adapt one line of a note, leaving link targets, support references, and quotes from other Bible versions unchanged.
    """
    adapter.lineNumber += 1
    return adapter.adaptProtected(line, lambda text: adaptUnprotectedNoteLine(text, adapter))
# end of adaptNoteLine


def adaptUnprotectedNoteLine(line:str, adapter:NameAdapter) -> str:
    pieces, lastEnd = [], 0
    for match in PROTECTED_RE.finditer(line):
        pieces.append(adapter.adaptNames(adapter.adaptTerminology(line[lastEnd:match.start()], adapter.terminologyRules)))
        pieces.append(match.group(0))
        lastEnd = match.end()
    pieces.append(adapter.adaptNames(adapter.adaptTerminology(line[lastEnd:], adapter.terminologyRules)))
    return ''.join(pieces)
# end of adaptUnprotectedNoteLine


def adaptTSVFile(filepath:Path, adapter:NameAdapter) -> None:
    """
    Adapt the Note column of each row (each row is a separate note).

    Notes use a literal backslash-n to separate their lines.
    """
    originalText = filepath.read_text(encoding='utf-8')
    lines = originalText.split('\n')
    for lineIndex, line in enumerate(lines):
        if lineIndex == 0 or not line: continue # Header or final empty line
        fields = line.split('\t')
        if len(fields) != NUM_COLUMNS:
            print(f"  WARNING: {filepath.name} line {lineIndex+1} has {len(fields)} fields (not {NUM_COLUMNS}) — left unchanged")
            continue
        adapter.newItem()
        fields[NOTE_COLUMN] = '\\n'.join(adaptNoteLine(noteLine, adapter) for noteLine in fields[NOTE_COLUMN].split('\\n'))
        lines[lineIndex] = '\t'.join(fields)
    newText = '\n'.join(lines)
    if newText != originalText:
        filepath.write_text(newText, encoding='utf-8')
# end of adaptTSVFile


def writeNotices(counts:Counter) -> None:
    enabledRules = [description for enabled, _regex, _replacement, description in TERMINOLOGY_RULES if enabled]
    notice = f"""# Adaptation notice

This repository contains an adaptation of the [unfoldingWord® Translation Notes](https://git.door43.org/unfoldingWord/en_tn)
(© unfoldingWord; see `uW_README.md` and `uW_LICENSE.md`),
which are licensed under [CC BY-SA 4.0](http://creativecommons.org/licenses/by-sa/4.0/).
These adaptations are released under the same licence.

## Changes made

These changes were made automatically by `adapt_uW_en_tn.py` (version {PROGRAM_VERSION})
to match the [Open English Translation](https://github.com/Freely-Given-org/OpenEnglishTranslation--OET) Readers’ Version (OET-RV):

- In the Note column, the OET-RV form of each name (from `OET-RV_names_table.tsv`) is given after a slash
  after the first use of the traditional name in each note (and again after about {EXPLAIN_WINDOW} lines of a long note),
  e.g., ‘Samuel/Shmuel’ then just ‘Samuel’. (The traditional names are kept because the notes refer to the ULT and UST.)
- Other OET-RV wording was added in parentheses after the first use of their term in each note, e.g., ‘the LORD (Yahweh)’:
""" + ''.join(f"  - {description}\n" for description in enabledRules) + """
The original-language quotes, link targets, support references, Bible book names in references (e.g., ‘John 1:19’),
and text quoted from other Bible versions (e.g., ‘“…” (NIV)’) were not changed.
See `adaptation_log.tsv` for the number of times each change was made.
"""
    (THIS_FOLDER / 'ADAPTATION_NOTICE.md').write_text(notice + sourceCorrectionsNotice(), encoding='utf-8')
    with open(THIS_FOLDER / 'adaptation_log.tsv', 'wt', encoding='utf-8') as logFile:
        logFile.write('Type\tChange\tCount\n')
        for key, count in sorted(counts.items(), key=lambda kc: (-kc[1], kc[0])):
            logFile.write(f'{key}\t{count}\n')
# end of writeNotices


def main() -> None:
    print(f"{PROGRAM_NAME} v{PROGRAM_VERSION} ({LAST_MODIFIED_DATE})")
    tsvPaths = copySourceFiles()
    names = loadNames(countEsfmWords())
    namesRE = makeNamesRegex(names)
    counts = Counter()
    applySourceCorrections(counts)
    adapter = NameAdapter(names, namesRE, counts, theirNameFirst=True, ownVersions=OWN_VERSIONS)
    for filepath in tsvPaths:
        adaptTSVFile(filepath, adapter)
    checkStrayBackslashes(tsvPaths)
    writeNotices(counts)
    numNameChanges = sum(count for key, count in counts.items() if key.startswith('NAME'))
    numTermChanges = sum(count for key, count in counts.items() if key.startswith('TERM'))
    print(f"  Adapted {len(tsvPaths)} files: made {numNameChanges:,} name changes and {numTermChanges:,} terminology changes (see adaptation_log.tsv)")
# end of main

if __name__ == '__main__':
    main()
# end of adapt_uW_en_tn.py
