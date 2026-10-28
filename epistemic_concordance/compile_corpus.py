#!/usr/bin/env python3
"""
BYTE-PINNED CORPUS COMPILER & STATIC SITE GENERATOR
Scripture (PD Douay-Rheims + KJV) <-> Catechism of Trent 1566 (PD rc-en.txt) <-> Vatican II <-> CCC Concordance
License: GNU AGPLv3
Attestation: probabilistic_structural
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Dict, List, Tuple

from bsar_xcube import BsarXCubeCompiler, EpistemicState, LuaAssociativeNode, canonical_sha256
from replicability_ledger import ZeroPiiSafetyFloor, build_resurrection_replicability_audit

import os

TRENT_SOURCE_PATH = Path(
    os.environ.get(
        "BSAR_TRENT_PATH",
        str(
            Path.home()
            / "Desktop"
            / "Synoptics"
            / "research"
            / "doctrinal-development"
            / "pilot-v1"
            / "eucharist"
            / "sources"
            / "rc-en.txt"
        ),
    )
)
BUNDLED_TRENT_SLICES_PATH = Path(__file__).resolve().parent / "trent_verified_slices.json"
EXPECTED_TRENT_SHA256 = "25c6fd3fedbb7297447ab2472112faa8e6409b9954c5315dbf25e79860656e27"


def load_verified_trent_lines(path: Path = TRENT_SOURCE_PATH) -> Tuple[List[str], str]:
    """Verify exact SHA-256 byte pin of the 1566 Roman Catechism (McHugh & Callan PD witness) before slicing."""
    raw_bytes = path.read_bytes()
    actual_sha = hashlib.sha256(raw_bytes).hexdigest()
    if actual_sha != EXPECTED_TRENT_SHA256:
        raise RuntimeError(
            f"Synoptics byte-pin mismatch on rc-en.txt! Expected {EXPECTED_TRENT_SHA256}, got {actual_sha}"
        )
    lines = raw_bytes.decode("utf-8").splitlines()
    return lines, actual_sha


def slice_trent(lines: List[str], start_1idx: int, end_1idx: int) -> Dict[str, Any]:
    """Extract an exact 1-indexed line slice from rc-en.txt with reversible line provenance."""
    chunk = "\n".join(lines[start_1idx - 1 : end_1idx]).strip()
    return {
        "source_file": "rc-en.txt (Catechism of the Council of Trent, 1566 — Public Domain)",
        "source_sha256": EXPECTED_TRENT_SHA256,
        "line_range": f"L{start_1idx}–L{end_1idx}",
        "editorial_warning": "Divisions/subheadings in the Fordham McHugh-Callan witness were supplied by translators, not the 1566 Manutian original (Synoptics PLAN.md §3).",
        "verbatim_text": chunk,
    }


def build_public_domain_bible_store() -> Dict[str, Dict[str, str]]:
    """
    100% Public-Domain verbatim Scripture store (Douay-Rheims 1899 Challoner + KJV 1769)
    with explicit 66-book Protestant/Reformed/Lutheran vs 73-book Deuterocanon tagging.
    """
    return {
        "GEN.1.1": {
            "ref": "Genesis 1:1",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "In the beginning God created heaven, and earth.",
            "kjv": "In the beginning God created the heaven and the earth.",
        },
        "EXO.20.2-3": {
            "ref": "Exodus 20:2–3",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "I am the Lord thy God, who brought thee out of the land of Egypt, out of the house of bondage. Thou shalt not have strange gods before me.",
            "kjv": "I am the LORD thy God, which have brought thee out of the land of Egypt, out of the house of bondage. Thou shalt have no other gods before me.",
        },
        "ISA.53.5": {
            "ref": "Isaiah 53:5",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "But he was wounded for our iniquities, he was bruised for our sins: the chastisement of our peace was upon him, and by his bruises we are healed.",
            "kjv": "But he was wounded for our transgressions, he was bruised for our iniquities: the chastisement of our peace was upon him; and with his stripes we are healed.",
        },
        "MAL.1.11": {
            "ref": "Malachi 1:11",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "For from the rising of the sun even to the going down, my name is great among the Gentiles, and in every place there is sacrifice, and there is offered to my name a clean oblation.",
            "kjv": "For from the rising of the sun even unto the going down of the same my name shall be great among the Gentiles; and in every place incense shall be offered unto my name, and a pure offering.",
        },
        "2MA.12.46": {
            "ref": "2 Maccabees 12:46",
            "canon": "DEUTEROCANON_7_BOOKS",
            "drb": "It is therefore a holy and wholesome thought to pray for the dead, that they may be loosed from sins.",
            "kjv": "[Deuterocanon / KJV Apocrypha] Wherefore he made a reconciliation for the dead, that they might be delivered from sin.",
        },
        "MAT.6.9-13": {
            "ref": "Matthew 6:9–13",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "Thus therefore shall you pray: Our Father who art in heaven, hallowed be thy name. Thy kingdom come. Thy will be done on earth as it is in heaven. Give us this day our supersubstantial bread. And forgive us our debts, as we also forgive our debtors. And lead us not into temptation. But deliver us from evil. Amen.",
            "kjv": "After this manner therefore pray ye: Our Father which art in heaven, Hallowed be thy name. Thy kingdom come. Thy will be done in earth, as it is in heaven. Give us this day our daily bread. And forgive us our debts, as we forgive our debtors. And lead us not into temptation, but deliver us from evil: For thine is the kingdom, and the power, and the glory, for ever. Amen.",
        },
        "MAT.18.21-35": {
            "ref": "Matthew 18:32–33",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "Wicked servant, I forgave thee all the debt, because thou besoughtest me: Shouldst not thou then have had compassion also on thy fellow servant, even as I had compassion on thee?",
            "kjv": "O thou wicked servant, I forgave thee all that debt, because thou desiredst me: Shouldest not thou also have had compassion on thy fellowservant, even as I had pity on thee?",
        },
        "MAT.26.26-28": {
            "ref": "Matthew 26:26–28",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "Take ye, and eat. This is my body. And taking the chalice, he gave thanks, and gave to them, saying: Drink ye all of this. For this is my blood of the new testament, which shall be shed for many unto remission of sins.",
            "kjv": "Take, eat; this is my body. And he took the cup, and gave thanks, and gave it to them, saying, Drink ye all of it; For this is my blood of the new testament, which is shed for many for the remission of sins.",
        },
        "MAT.28.1-8": {
            "ref": "Matthew 28:5–6",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "Fear not you; for I know that you seek Jesus that was crucified. He is not here, for he is risen, as he said.",
            "kjv": "Fear not ye: for I know that ye seek Jesus, which was crucified. He is not here: for he is risen, as he said.",
        },
        "MAT.28.19": {
            "ref": "Matthew 28:19",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "Going therefore, teach ye all nations; baptizing them in the name of the Father, and of the Son, and of the Holy Ghost.",
            "kjv": "Go ye therefore, and teach all nations, baptizing them in the name of the Father, and of the Son, and of the Holy Ghost.",
        },
        "MRK.16.1-8": {
            "ref": "Mark 16:6",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "Be not affrighted; you seek Jesus of Nazareth, who was crucified: he is risen, he is not here, behold the place where they laid him.",
            "kjv": "Be not affrighted: Ye seek Jesus of Nazareth, which was crucified: he is risen; he is not here: behold the place where they laid him.",
        },
        "JHN.1.1-14": {
            "ref": "John 1:1, 14",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "In the beginning was the Word, and the Word was with God, and the Word was God... And the Word was made flesh, and dwelt among us.",
            "kjv": "In the beginning was the Word, and the Word was with God, and the Word was God... And the Word was made flesh, and dwelt among us.",
        },
        "JHN.3.5": {
            "ref": "John 3:5",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "Amen, amen I say to thee, unless a man be born again of water and the Holy Ghost, he cannot enter into the kingdom of God.",
            "kjv": "Verily, verily, I say unto thee, Except a man be born of water and of the Spirit, he cannot enter into the kingdom of God.",
        },
        "JHN.3.16": {
            "ref": "John 3:16",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "For God so loved the world, as to give his only begotten Son; that whosoever believeth in him, may not perish, but may have life everlasting.",
            "kjv": "For God so loved the world, that he gave his only begotten Son, that whosoever believeth in him should not perish, but have everlasting life.",
        },
        "JHN.6.51-56": {
            "ref": "John 6:51, 55",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "I am the living bread which came down from heaven. If any man eat of this bread, he shall live for ever; and the bread that I will give, is my flesh, for the life of the world... For my flesh is meat indeed: and my blood is drink indeed.",
            "kjv": "I am the living bread which came down from heaven: if any man eat of this bread, he shall live for ever: and the bread that I will give is my flesh, which I will give for the life of the world... For my flesh is meat indeed, and my blood is drink indeed.",
        },
        "ROM.3.23-28": {
            "ref": "Romans 3:24, 28",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "Being justified freely by his grace, through the redemption, that is in Christ Jesus... For we account a man to be justified by faith, without the works of the law.",
            "kjv": "Being justified freely by his grace through the redemption that is in Christ Jesus... Therefore we conclude that a man is justified by faith without the deeds of the law.",
        },
        "ROM.5.8": {
            "ref": "Romans 5:8",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "But God commendeth his charity towards us; because when as yet we were sinners, according to the time, Christ died for us.",
            "kjv": "But God commendeth his love toward us, in that, while we were yet sinners, Christ died for us.",
        },
        "1CO.3.15": {
            "ref": "1 Corinthians 3:15",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "If any man's work burn, he shall suffer loss; but he himself shall be saved, yet so as by fire.",
            "kjv": "If any man's work shall be burned, he shall suffer loss: but he himself shall be saved; yet so as by fire.",
        },
        "1CO.10.16": {
            "ref": "1 Corinthians 10:16",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "The chalice of benediction, which we bless, is it not the communion of the blood of Christ? And the bread, which we break, is it not the partaking of the body of the Lord?",
            "kjv": "The cup of blessing which we bless, is it not the communion of the blood of Christ? The bread which we break, is it not the communion of the body of Christ?",
        },
        "1CO.11.23-29": {
            "ref": "1 Corinthians 11:23–27",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "For I have received of the Lord that which also I delivered unto you, that the Lord Jesus, the same night in which he was betrayed, took bread... Whosoever shall eat this bread, or drink the chalice of the Lord unworthily, shall be guilty of the body and of the blood of the Lord.",
            "kjv": "For I have received of the Lord that which also I delivered unto you, That the Lord Jesus the same night in which he was betrayed took bread... Wherefore whosoever shall eat this bread, and drink this cup of the Lord, unworthily, shall be guilty of the body and blood of the Lord.",
        },
        "1CO.15.3-8": {
            "ref": "1 Corinthians 15:3–8",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "For I delivered unto you first of all, which I also received: how that Christ died for our sins, according to the scriptures: And that he was buried, and that he rose again the third day, according to the scriptures: And that he was seen by Cephas; and after that by the eleven. Then he was seen by more than five hundred brethren at once... And last of all, he was seen also by me.",
            "kjv": "For I delivered unto you first of all that which I also received, how that Christ died for our sins according to the scriptures; And that he was buried, and that he rose again the third day according to the scriptures: And that he was seen of Cephas, then of the twelve: After that, he was seen of above five hundred brethren at once... And last of all he was seen of me also.",
        },
        "1CO.15.14-17": {
            "ref": "1 Corinthians 15:14, 17",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "And if Christ be not risen again, then is our preaching vain, and your faith is also vain... And if Christ be not risen again, your faith is vain, for you are yet in your sins.",
            "kjv": "And if Christ be not risen, then is our preaching vain, and your faith is also vain... And if Christ be not raised, your faith is vain; ye are yet in your sins.",
        },
        "GAL.1.13-19": {
            "ref": "Galatians 1:13, 18–19",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "For you have heard of my conversation in time past in the Jews' religion: how that, beyond measure, I persecuted the church of God, and wasted it... Then, after three years, I went to Jerusalem to see Peter, and I tarried with him fifteen days. But other of the apostles I saw none, saving James the brother of the Lord.",
            "kjv": "For ye have heard of my conversation in time past in the Jews' religion, how that beyond measure I persecuted the church of God, and wasted it... Then after three years I went up to Jerusalem to see Peter, and abode with him fifteen days. But other of the apostles saw I none, save James the Lord's brother.",
        },
        "EPH.2.8-10": {
            "ref": "Ephesians 2:8–10",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "For by grace you are saved through faith, and that not of yourselves, for it is the gift of God; Not of works, that no man may glory. For we are his workmanship, created in Christ Jesus in good works, which God hath prepared that we should walk in them.",
            "kjv": "For by grace are ye saved through faith; and that not of yourselves: it is the gift of God: Not of works, lest any man should boast. For we are his workmanship, created in Christ Jesus unto good works, which God hath before ordained that we should walk in them.",
        },
        "COL.2.14": {
            "ref": "Colossians 2:14",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "Blotting out the handwriting of the decree that was against us, which was contrary to us. And he hath taken the same out of the way, fastening it to the cross.",
            "kjv": "Blotting out the handwriting of ordinances that was against us, which was contrary to us, and took it out of the way, nailing it to his cross.",
        },
        "TIT.3.5": {
            "ref": "Titus 3:5",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "Not by the works of justice, which we have done, but according to his mercy, he saved us, by the laver of regeneration, and renovation of the Holy Ghost.",
            "kjv": "Not by works of righteousness which we have done, but according to his mercy he saved us, by the washing of regeneration, and renewing of the Holy Ghost.",
        },
        "JAS.2.24": {
            "ref": "James 2:24",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "Do you see that by works a man is justified; and not by faith only?",
            "kjv": "Ye see then how that by works a man is justified, and not by faith only.",
        },
        "2PE.1.4": {
            "ref": "2 Peter 1:4",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "By whom he hath given us most great and precious promises: that by these you may be made partakers of the divine nature: flying the corruption of that concupiscence which is in the world.",
            "kjv": "Whereby are given unto us exceeding great and precious promises: that by these ye might be partakers of the divine nature, having escaped the corruption that is in the world through lust.",
        },
        "ISA.43.10": {
            "ref": "Isaiah 43:10",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "You are my witnesses, saith the Lord, and my servant whom I have chosen: that you may know, and believe me, and understand that I myself am. Before me there was no God formed, and after me there shall be none.",
            "kjv": "Ye are my witnesses, saith the LORD, and my servant whom I have chosen: that ye may know and believe me, and understand that I am he: before me there was no God formed, neither shall there be after me.",
        },
        "JHN.4.24": {
            "ref": "John 4:24",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "God is a spirit; and they that adore him, must adore him in spirit and in truth.",
            "kjv": "God is a Spirit: and they that worship him must worship him in spirit and in truth.",
        },
        "ROM.8.19-21": {
            "ref": "Romans 8:19–21",
            "canon": "ECUMENICAL_66_SHARED",
            "drb": "For the expectation of the creature waiteth for the revelation of the sons of God... Because the creature also itself shall be delivered from the servitude of corruption, into the liberty of the glory of the children of God.",
            "kjv": "For the earnest expectation of the creature waiteth for the manifestation of the sons of God... Because the creature itself also shall be delivered from the bondage of corruption into the glorious liberty of the children of God.",
        },
    }


def build_concordance_bundle() -> Dict[str, Any]:
    safety = ZeroPiiSafetyFloor()
    bible_store = build_public_domain_bible_store()

    if TRENT_SOURCE_PATH.exists():
        trent_lines, trent_sha = load_verified_trent_lines()
        trent_passages: Dict[str, Dict[str, Any]] = {
            "TRENT_P1_ART1_CREATOR": {
                "title": "Part I, Art. I — One God, Trinity & Creation",
                **slice_trent(trent_lines, 2983, 3028),
            },
            "TRENT_P1_ART4_SATISFACTION": {
                "title": "Part I, Art. IV — Fruits of Christ's Passion & Over-Solvent Ransom",
                **slice_trent(trent_lines, 4236, 4284),
            },
            "TRENT_P1_ART5_PURGATORY": {
                "title": "Part I, Art. V — Three Abodes & Purgatorial Cleansing",
                **slice_trent(trent_lines, 4341, 4360),
            },
            "TRENT_P1_ART5_RESURRECTION": {
                "title": "Part I, Art. V — The Third Day He Rose Again According to the Scriptures",
                **slice_trent(trent_lines, 4424, 4518),
            },
            "TRENT_P2_BAPTISM": {
                "title": "Part II — The Sacrament of Baptism (Water & Regeneration)",
                **slice_trent(trent_lines, 7160, 7215),
            },
            "TRENT_P2_EUCHARIST": {
                "title": "Part II — The Sacrament of the Eucharist (Institution & Real Presence)",
                **slice_trent(trent_lines, 8719, 8796),
            },
            "TRENT_P3_CMD1": {
                "title": "Part III — The First Commandment (True Worship & Conscience)",
                **slice_trent(trent_lines, 13331, 13380),
            },
            "TRENT_P4_PETITION5_DEBTS": {
                "title": "Part IV — Fifth Petition: Forgive Us Our Debts, As We Forgive",
                **slice_trent(trent_lines, 18902, 18958),
            },
        }
    else:
        trent_sha = EXPECTED_TRENT_SHA256
        trent_passages = json.loads(BUNDLED_TRENT_SLICES_PATH.read_text(encoding="utf-8"))

    compiler = BsarXCubeCompiler()

    # 1. CCC § 253 — Holy Trinity (Pillar I: Creed)
    n253 = LuaAssociativeNode(
        253,
        pillar="I_CREED",
        topic="The Dogma of the Holy Trinity (Unity & Tri-Personal Distinction)",
        summary="The Trinity is One God in three distinct Persons who do not divide the one divine substance.",
        trent_ref_id="TRENT_P1_ART1_CREATOR",
        vatican_en_url="https://www.vatican.va/archive/ENG0015/__P17.HTM",
        vatican_lt_url="https://www.vatican.va/archive/catechismus_lt/p1s2c1p2_lt.htm",
        tradition_lenses={
            "catholic": "Reaffirmed verbatim across Nicaea (325), Trent Part I Art. I, and CCC §§ 253–255.",
            "lutheran": "100% Shared Core (Augsburg Confession Art. I — Das kleine Evangelium rests on Triune self-giving).",
            "reformed_carm": "100% Shared Core (CARM Trinitarian orthodoxy chart: 1 God in 3 co-equal, co-eternal Persons).",
            "skeptic_note": "Newman Dossier 1 (Petavius): technical distinction of Persons protects rather than dissolves monotheistic Unity.",
        },
        newman_profile={
            "N1_Preservation_of_Type": "ATTESTED (Protects monotheistic Unity via relational distinction)",
            "N2_Continuity_of_Principles": "ATTESTED (Incarnational revelation vs rationalist reduction)",
            "N4_Logical_Sequence": "ATTESTED (Baptismal formula + Johannine Logos -> Nicene Homoousios)",
            "verdict_category": "EQUIVALENT_REAFFIRMED_ACROSS_NICENE_TRADITIONS",
        },
    )
    n253.add_thread(verse_ref="GEN.1.1", cluster_id="CL_CREATOR_MONOTHEISM", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="NICAEA_325", newman_note="N1_PRESERVATION_OF_TYPE", decibans=5.0)
    n253.add_thread(verse_ref="MAT.28.19", cluster_id="CL_TRIUNE_BAPTISM_NAME", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="DIRECT_SCRIPTURE", newman_note="N0_EXPLICIT_KERYGMA", decibans=9.5)
    n253.add_thread(verse_ref="JHN.1.1-14", cluster_id="CL_JOHANNINE_LOGOS", warrant_mode="DEDUCTIVE_PROOF", canon_scope="ECUMENICAL_66_SHARED", mediator="ATHANASIUS_NICAEA", newman_note="N4_LOGICAL_SEQUENCE", decibans=9.0)
    n253.add_thread(verse_ref="ISA.43.10", cluster_id="CL_CREATOR_MONOTHEISM", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="NICAEA_325", newman_note="N1_PRESERVATION_OF_TYPE", decibans=8.8)
    n253.add_thread(verse_ref="JHN.4.24", cluster_id="CL_DIVINE_INCORPOREALITY", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="TRENT_ART_I", newman_note="N1_PRESERVATION_OF_TYPE", decibans=8.2)
    compiler.register_node(n253)

    # 1B. CCC § 460 — Participatory Theosis vs. Frontier Species-Exaltation (Pillar I: Creed)
    n460 = LuaAssociativeNode(
        460,
        pillar="I_CREED",
        topic="Participatory Divinization (Theosis — 2 Pet 1:4) vs. Becoming Uncreated Gods",
        summary="The Word became flesh to make humans partakers of the divine nature by grace and adoption, without erasing the Creator-creature boundary.",
        trent_ref_id="TRENT_P1_ART1_CREATOR",
        vatican_en_url="https://www.vatican.va/archive/ENG0015/__P1J.HTM",
        vatican_lt_url="https://www.vatican.va/archive/catechismus_lt/p1s2c2a3_lt.htm",
        tradition_lenses={
            "catholic": "CCC § 460 (quoting St. Athanasius De Incarnatione 54:3 & Aquinas): Humans share divine life by grace/adoption, NEVER by becoming independent uncreated gods.",
            "lutheran": "Union with Christ / Indwelling (Luther's 1514 Christmas Sermon): Real participation in Christ's righteousness and glory while God alone remains Creator.",
            "reformed_carm": "CARM explicitly contrasts biblical union/glorification (2 Pet 1:4; Rom 8:19–21) against LDS King Follett ontological godhood (Isa 43:10).",
            "skeptic_note": "Anchors Tab 5's exact razor: why ancient patristic Theosis + cosmic stewardship is Nicene `1`/`?`, while contingent creator-gods is Nicene `0`!",
        },
        newman_profile={
            "N1_Preservation_of_Type": "ATTESTED (Creator/creature ontological boundary strictly preserved via grace-by-adoption)",
            "N3_Power_of_Assimilation": "ATTESTED (Distinguishes Christian Theosis cleanly from pagan/frontier apotheosis)",
            "verdict_category": "NICENE_CREATOR_CREATURE_BOUNDARY_ANCHOR",
        },
    )
    n460.add_thread(verse_ref="2PE.1.4", cluster_id="CL_PARTAKERS_DIVINE_NATURE", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="ATHANASIUS_DE_INC_54", newman_note="N1_PRESERVATION_OF_TYPE", decibans=9.6)
    n460.add_thread(verse_ref="JHN.1.1-14", cluster_id="CL_JOHANNINE_LOGOS", warrant_mode="DEDUCTIVE_PROOF", canon_scope="ECUMENICAL_66_SHARED", mediator="IRENAEUS_ADV_HAER", newman_note="N2_CONTINUITY_OF_PRINCIPLES", decibans=9.0)
    n460.add_thread(verse_ref="ISA.43.10", cluster_id="CL_CREATOR_MONOTHEISM", warrant_mode="DEDUCTIVE_PROOF", canon_scope="ECUMENICAL_66_SHARED", mediator="NICAEA_325", newman_note="N6_CONSERVATIVE_ACTION", decibans=8.8)
    n460.add_thread(verse_ref="ROM.8.19-21", cluster_id="CL_COSMIC_GLORIFICATION", warrant_mode="DEDUCTIVE_PROOF", canon_scope="ECUMENICAL_66_SHARED", mediator="DIRECT_SCRIPTURE", newman_note="N5_ANTICIPATION_OF_FUTURE", decibans=7.8)
    compiler.register_node(n460)

    # 2. CCC § 604 — Redemptive Love & John 3:16 Over-Solvent Exchange (Pillar I: Creed)
    n604 = LuaAssociativeNode(
        604,
        pillar="I_CREED",
        topic="God's Redemptive Initiative & The Over-Solvent Cross (John 3:16 Core)",
        summary="In giving His Son for our sins, God manifests that His redemptive plan precedes all human merit and flows from pure love.",
        trent_ref_id="TRENT_P1_ART4_SATISFACTION",
        vatican_en_url="https://www.vatican.va/archive/ENG0015/__P1O.HTM",
        vatican_lt_url="https://www.vatican.va/archive/catechismus_lt/p1s2c2a4_lt.htm",
        tradition_lenses={
            "catholic": "Trent (L4269–L4271) & CCC § 604: Christ's satisfaction was not merely equal to our debt, 'but far exceeded them', preceding all human merit.",
            "lutheran": "100% Heart of Scripture ('Das kleine Evangelium' — Luther's Joyous Exchange: Sovereign Principal absorbs terminal Debit in full).",
            "reformed_carm": "Strong Shared Core on Christ's substitutionary satisfaction & unmerited divine initiative (carm.org/atonement); debates extent/imputation mechanics.",
            "skeptic_note": "In 2D Debit/Credit moralism, unilateral debt assumption looks 'too good to be true'; double-entry conservation holds because the Principal pays on His own sheet.",
        },
        newman_profile={
            "N1_Preservation_of_Type": "ATTESTED (Kerygmatic gift precedes moral law)",
            "N6_Conservative_Action_on_Past": "ATTESTED (Conserves divine justice while fulfilling mercy)",
            "verdict_category": "SHARED_ECUMENICAL_BEDROCK",
        },
    )
    n604.add_thread(verse_ref="JHN.3.16", cluster_id="CL_JOHN_3_16_GIFT", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="DIRECT_SCRIPTURE", newman_note="N0_EXPLICIT_KERYGMA", decibans=11.0)
    n604.add_thread(verse_ref="ROM.5.8", cluster_id="CL_PAUL_WHILE_SINNERS", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="TRENT_ART_IV", newman_note="N0_EXPLICIT_KERYGMA", decibans=9.5)
    n604.add_thread(verse_ref="ISA.53.5", cluster_id="CL_SUFFERING_SERVANT", warrant_mode="TYPOLOGICAL_FULFILLMENT", canon_scope="ECUMENICAL_66_SHARED", mediator="DIRECT_SCRIPTURE", newman_note="N5_ANTICIPATION_OF_FUTURE", decibans=7.5)
    n604.add_thread(verse_ref="COL.2.14", cluster_id="CL_DEBT_BOND_CANCELLED", warrant_mode="DEDUCTIVE_PROOF", canon_scope="ECUMENICAL_66_SHARED", mediator="TRENT_ART_IV", newman_note="N6_CONSERVATIVE_ACTION", decibans=8.5)
    compiler.register_node(n604)

    # 3. CCC § 639 — Historical & Transcendent Reality of the Resurrection (Pillar I: Creed)
    n639 = LuaAssociativeNode(
        639,
        pillar="I_CREED",
        topic="The Empty Tomb & Eyewitness Testimony of the Bodily Resurrection",
        summary="The mystery of Christ's bodily Resurrection is a real historical event attested by the New Testament through the empty tomb and concrete eyewitness encounters.",
        trent_ref_id="TRENT_P1_ART5_RESURRECTION",
        vatican_en_url="https://www.vatican.va/archive/ENG0015/__P1R.HTM",
        vatican_lt_url="https://www.vatican.va/archive/catechismus_lt/p1s2c2a5_lt.htm",
        tradition_lenses={
            "catholic": "Trent Art. V (L4498–L4508) & CCC §§ 638–658: Historical bodily resurrection 'according to the Scriptures' is the hinge of Christian faith.",
            "lutheran": "100% Shared Core: Bodily victory over death & hell; without 1 Cor 15:14, preaching and faith are empty.",
            "reformed_carm": "100% Shared Core (Matt Slick / CARM Resurrection tables: early 1 Cor 15 creed, empty tomb, hostile Paul conversion, apostolic martyrdom).",
            "skeptic_note": "Tested directly in the Hume 'Of Miracles' (@PAHoyeck) Psychometric Replicability Lab: literary parallels deduplicated, independent costly channels multiplied.",
        },
        newman_profile={
            "N1_Preservation_of_Type": "ATTESTED (Apostolic kerygma identical in 1 Cor 15, Trent, and CCC)",
            "N7_Chronic_Vigour": "ATTESTED (Athanasius De Incarnatione §§ 27–32 observable phase transition)",
            "verdict_category": "EQUIVALENT_REAFFIRMED_PLUS_REPLICABILITY_TESTED",
        },
    )
    n639.add_thread(verse_ref="1CO.15.3-8", cluster_id="CL_EARLY_JERUSALEM_KERYGMA", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="DIRECT_SCRIPTURE", newman_note="N0_EXPLICIT_KERYGMA", decibans=11.8)
    n639.add_thread(verse_ref="1CO.15.14-17", cluster_id="CL_EARLY_JERUSALEM_KERYGMA", warrant_mode="DEDUCTIVE_PROOF", canon_scope="ECUMENICAL_66_SHARED", mediator="TRENT_ART_V", newman_note="N4_LOGICAL_SEQUENCE", decibans=10.5)
    n639.add_thread(verse_ref="MRK.16.1-8", cluster_id="CL_SYNOPTIC_EMPTY_TOMB_WOMEN", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="DIRECT_SCRIPTURE", newman_note="N0_EXPLICIT_KERYGMA", decibans=10.2)
    n639.add_thread(verse_ref="MAT.28.1-8", cluster_id="CL_SYNOPTIC_EMPTY_TOMB_WOMEN", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="DIRECT_SCRIPTURE", newman_note="N0_EXPLICIT_KERYGMA", decibans=10.2)
    n639.add_thread(verse_ref="GAL.1.13-19", cluster_id="CL_HOSTILE_OUTGROUP_PAUL", warrant_mode="DEDUCTIVE_PROOF", canon_scope="ECUMENICAL_66_SHARED", mediator="ATHANASIUS_DE_INC", newman_note="N7_CHRONIC_VIGOUR", decibans=15.0)
    compiler.register_node(n639)

    # 4. CCC § 1030–1032 — Final Purification / Purgatory (Deuterocanon + Hermeneutical Crux)
    n1031 = LuaAssociativeNode(
        1031,
        pillar="I_CREED",
        topic="Final Purification (Purgatory) & Prayer for the Dead — Classic Ecumenical Crux",
        summary="Those who die in God's grace and friendship, yet imperfectly purified, undergo purification to achieve the holiness needed to enter heaven.",
        trent_ref_id="TRENT_P1_ART5_PURGATORY",
        vatican_en_url="https://www.vatican.va/archive/ENG0015/__P2N.HTM",
        vatican_lt_url="https://www.vatican.va/archive/catechismus_lt/p1s2c3a12_lt.htm",
        tradition_lenses={
            "catholic": "Trent Art. V (L4348–L4353) & CCC §§ 1030–1032: Combines Deuterocanonical 2 Macc 12:46 with Protocanonical 1 Cor 3:15 and ancient liturgical practice.",
            "lutheran": "Disputed / Rejected (Smalcald Articles Part II Art. II): Rejects temporal satisfaction after death on 66-book canon + sufficiency of John 3:16.",
            "reformed_carm": "Explicitly Contested on CARM (carm.org/purgatory): Rejects 2 Maccabees as non-canonical and reads 1 Cor 3:15 as testing of ministerial works, not post-mortem cleansing.",
            "skeptic_note": "Clean demonstration of why our XCube separates `canon_scope` (66 vs 73 books) from `warrant_mode` (inferential vs explicit) so nobody talks past each other!",
        },
        newman_profile={
            "N2_Continuity_of_Principles": "CONTESTED_ACROSS_CANON_BOUNDARY (Sacramental sanctification vs Forensic completeness)",
            "N5_Anticipation_of_Future": "ATTESTED_IN_LITURGY (Early Christian catacomb prayers & Perpetua)",
            "verdict_category": "CANON_AND_HERMENEUTICAL_CRUX_PRESERVING_OPPOSING_READINGS",
        },
    )
    n1031.add_thread(verse_ref="2MA.12.46", cluster_id="CL_MACCABEES_PRAYER_DEAD", warrant_mode="DIRECT_QUOTE", canon_scope="DEUTEROCANON_7_BOOKS", mediator="TRENT_SESSION_XXV", newman_note="N5_ANTICIPATION_OF_FUTURE", decibans=8.0)
    n1031.add_thread(verse_ref="1CO.3.15", cluster_id="CL_PAUL_SAVED_AS_BY_FIRE", warrant_mode="DEDUCTIVE_PROOF", canon_scope="ECUMENICAL_66_SHARED", mediator="FLORENCE_TRENT", newman_note="N4_LOGICAL_SEQUENCE", decibans=4.0)
    compiler.register_node(n1031)

    # 5. CCC § 1213 — Sacrament of Baptism (Pillar II: Sacraments)
    n1213 = LuaAssociativeNode(
        1213,
        pillar="II_SACRAMENTS",
        topic="Holy Baptism — Doorway of Spiritual Regeneration by Water and the Spirit",
        summary="Holy Baptism is the foundational sacrament of the Christian life, freeing from sin and regenerating the believer as a child of God.",
        trent_ref_id="TRENT_P2_BAPTISM",
        vatican_en_url="https://www.vatican.va/archive/ENG0015/__P3J.HTM",
        vatican_lt_url="https://www.vatican.va/archive/catechismus_lt/p2s2c1a1_lt.htm",
        tradition_lenses={
            "catholic": "Trent Part II (L7160+) & CCC § 1213: Instrumental sacrament of regeneration instituted by Christ.",
            "lutheran": "Strong Sacramental Overlap (Small Catechism on Baptism: 'works forgiveness of sins, rescues from death and the devil' via God's Word bound to water).",
            "reformed_carm": "Partial Crux: Affirms Trinitarian water baptism as covenantal sign & seal (Westminster 28), while rejecting ex opere operato baptismal regeneration.",
            "skeptic_note": "Newman Dossier 3 notes Luther retained the ancient sacramental principle on Baptism & Eucharist against rationalist reduction.",
        },
        newman_profile={
            "N1_Preservation_of_Type": "ATTESTED (Water + Trinitarian invocation conserved from 1st century)",
            "N2_Continuity_of_Principles": "ATTESTED (Sacramental mediation through physical matter)",
            "verdict_category": "CATHOLIC_LUTHERAN_CONVERGENCE_REFORMED_SIGN_SEAL_DISTINCTION",
        },
    )
    n1213.add_thread(verse_ref="JHN.3.5", cluster_id="CL_NICODEMUS_WATER_SPIRIT", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="TRENT_BAPTISM", newman_note="N0_EXPLICIT_KERYGMA", decibans=8.5)
    n1213.add_thread(verse_ref="TIT.3.5", cluster_id="CL_TITUS_WASHING_REGEN", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="DIRECT_SCRIPTURE", newman_note="N2_CONTINUITY_OF_PRINCIPLES", decibans=7.8)
    n1213.add_thread(verse_ref="MAT.28.19", cluster_id="CL_TRIUNE_BAPTISM_NAME", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="DIDACHE_7", newman_note="N1_PRESERVATION_OF_TYPE", decibans=9.0)
    compiler.register_node(n1213)

    # 6. CCC § 1374 — The Eucharist & Real Presence (Pillar II: Sacraments — Hermes Pilot Track E)
    n1374 = LuaAssociativeNode(
        1374,
        pillar="II_SACRAMENTS",
        topic="The Most Holy Eucharist — Real & Substantial Presence of Christ",
        summary="In the blessed sacrament of the Eucharist, the body and blood, together with the soul and divinity of Christ, are truly, really, and substantially contained.",
        trent_ref_id="TRENT_P2_EUCHARIST",
        vatican_en_url="https://www.vatican.va/archive/ENG0015/__P41.HTM",
        vatican_lt_url="https://www.vatican.va/archive/catechismus_lt/p2s2c1a3_lt.htm",
        tradition_lenses={
            "catholic": "Trent Session XIII / Roman Catechism (L8719–L8796) -> Sacrosanctum Concilium -> CCC § 1374: Doctrinal core reaffirmed; liturgical rite revised in 1969.",
            "lutheran": "High Real-Presence Overlap (Sacramental Union 'in, with, and under' bread and wine; Luther stood on 'This IS my body' at Marburg 1529 while declining Aristotelian transubstantiation).",
            "reformed_carm": "Explicit Crux on CARM: Rejects bodily transubstantiation & Eucharistic sacrifice; affirms spiritual nourishment by faith (Calvin) or memorial.",
            "skeptic_note": "Prime showcase of Newman's 'Cable of Independent Strands': Synoptic institution + Pauline 1 Cor 10–11 + Johannine John 6 + Malachi 1:11 + Ignatius of Antioch.",
        },
        newman_profile={
            "N1_Preservation_of_Type": "ATTESTED_DOCTRINAL_CORE (Disciplinary/ceremonial shifts tracked separately per Synoptics PLAN.md §5A)",
            "N3_Power_of_Assimilation": "ATTESTED_OR_CONTESTED (Uses 'substance' to guard literal 'This is My body')",
            "verdict_category": "EQUIVALENT_DOCTRINE_TRENT_TO_CCC_WITH_REFORMATION_METAPHYSICAL_CRUX",
        },
    )
    n1374.add_thread(verse_ref="MAT.26.26-28", cluster_id="CL_LAST_SUPPER_INSTITUTION", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="TRENT_SESSION_XIII", newman_note="N0_EXPLICIT_KERYGMA", decibans=9.2)
    n1374.add_thread(verse_ref="JHN.6.51-56", cluster_id="CL_BREAD_OF_LIFE_DISCOURSE", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="IGNATIUS_SMYRN_7", newman_note="N2_CONTINUITY_OF_PRINCIPLES", decibans=9.0)
    n1374.add_thread(verse_ref="1CO.10.16", cluster_id="CL_PAUL_EUCHARISTIC_KOINONIA", warrant_mode="DEDUCTIVE_PROOF", canon_scope="ECUMENICAL_66_SHARED", mediator="TRENT_EUCHARIST", newman_note="N4_LOGICAL_SEQUENCE", decibans=8.4)
    n1374.add_thread(verse_ref="1CO.11.23-29", cluster_id="CL_PAUL_EUCHARISTIC_KOINONIA", warrant_mode="DEDUCTIVE_PROOF", canon_scope="ECUMENICAL_66_SHARED", mediator="SACROSANCTUM_CONCILIUM", newman_note="N6_CONSERVATIVE_ACTION", decibans=8.6)
    n1374.add_thread(verse_ref="MAL.1.11", cluster_id="CL_MALACHI_PURE_OFFERING", warrant_mode="TYPOLOGICAL_FULFILLMENT", canon_scope="ECUMENICAL_66_SHARED", mediator="DIDACHE_14_TRENT_XXII", newman_note="N5_ANTICIPATION_OF_FUTURE", decibans=6.2)
    compiler.register_node(n1374)

    # 7. CCC § 1996 — Justification & Free Gift of Grace (Pillar III: Life in Christ)
    n1996 = LuaAssociativeNode(
        1996,
        pillar="III_LIFE_IN_CHRIST",
        topic="Justification by God's Free Grace vs. Faith & Works (Rom 3 / Eph 2 / Jas 2)",
        summary="Our justification comes from the grace of God alone as a free, undeserved gift uniting us to Christ's righteousness and renewing the inner person.",
        trent_ref_id="TRENT_P1_ART4_SATISFACTION",
        vatican_en_url="https://www.vatican.va/archive/ENG0015/__P6Z.HTM",
        vatican_lt_url="https://www.vatican.va/archive/catechismus_lt/p3s1c3a2_lt.htm",
        tradition_lenses={
            "catholic": "Trent Session VI & CCC §§ 1996–2005: Initial justification is 100% unmerited grace (Rom 3:24; Eph 2:8); grace truly transforms and bears fruit in charity (Jas 2:24).",
            "lutheran": "1999 Joint Declaration on the Doctrine of Justification (JDDJ): High convergence on unmerited grace; Lutheranism guards forensic assurance against anxious merit-counting.",
            "reformed_carm": "Core Reformation Debate on CARM (carm.org/justification): Distinguishes forensic imputation (Rom 3:28; Eph 2:8–9) strictly from sanctification (Eph 2:10; Jas 2:24 as fruit/evidence of living faith, never ground of justification).",
            "skeptic_note": "Notice how putting Rom 3:28, Eph 2:8–10, and Jas 2:24 in the SAME 66-book slice reveals the exact lexical distinction ('ground' vs 'transformative union') rather than straw-men!",
        },
        newman_profile={
            "N2_Continuity_of_Principles": "CONTESTED_DEFINITIONAL_SCOPE ('dikaioun' = declare righteous vs make righteous)",
            "N6_Conservative_Action_on_Past": "ATTESTED (Integrates Paul on unmerited grace + James on living faith)",
            "verdict_category": "DEFINITIONAL_SCOPE_CRUX_WITH_SHARED_ANTI_PELAGIAN_FLOOR",
        },
    )
    n1996.add_thread(verse_ref="ROM.3.23-28", cluster_id="CL_PAUL_GRACE_WITHOUT_LAW", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="TRENT_SESSION_VI", newman_note="N0_EXPLICIT_KERYGMA", decibans=10.0)
    n1996.add_thread(verse_ref="EPH.2.8-10", cluster_id="CL_EPHESIANS_GRACE_WORKMANSHIP", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="DIRECT_SCRIPTURE", newman_note="N6_CONSERVATIVE_ACTION", decibans=10.2)
    n1996.add_thread(verse_ref="JHN.3.16", cluster_id="CL_JOHN_3_16_GIFT", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="DIRECT_SCRIPTURE", newman_note="N0_EXPLICIT_KERYGMA", decibans=9.8)
    n1996.add_thread(verse_ref="JAS.2.24", cluster_id="CL_JAMES_LIVING_FAITH", warrant_mode="DEDUCTIVE_PROOF", canon_scope="ECUMENICAL_66_SHARED", mediator="TRENT_SESSION_VI", newman_note="N4_LOGICAL_SEQUENCE", decibans=7.5)
    compiler.register_node(n1996)

    # 8. CCC § 2106 — Religious Freedom & Immunity from Coercion (Pillar III — Hermes Pilot Track R)
    n2106 = LuaAssociativeNode(
        2106,
        pillar="III_LIFE_IN_CHRIST",
        topic="Religious Liberty & Immunity from Civil Coercion (Trent -> Dignitatis Humanae -> CCC)",
        summary="Nobody may be forced to act against their convictions in religious matters within just limits, grounded in the dignity of the human person.",
        trent_ref_id="TRENT_P3_CMD1",
        vatican_en_url="https://www.vatican.va/archive/ENG0015/__P7D.HTM",
        vatican_lt_url="https://www.vatican.va/archive/catechismus_lt/p3s2c1a1_lt.htm",
        tradition_lenses={
            "catholic": "Hermes Synoptics Hard Case (PLAN.md §5B): Dignitatis Humanae §1–2 distinguishes moral duty toward true religion (First Commandment, unchanged) from civil state coercion; rupture critics cite Quanta Cura (1864).",
            "lutheran": "Two-Kingdoms Resonance: Sword of civil magistrate cannot coerce inward faith (*fiducia* requires uncoerced conscience).",
            "reformed_carm": "Westminster Confession Ch. 20 ('God alone is Lord of the conscience') strongly affirms uncoerced conscience in matters of faith.",
            "skeptic_note": "Sweetbrier Node 0 Invariant: Human dignity forbids coercive override; preserves both continuity reconciliation and 19th-century tension dossier openly.",
        },
        newman_profile={
            "N1_Preservation_of_Type": "APPARENT_TENSION_TESTED_BY_JURISDICTION_SCOPE (Moral duty vs Civil police power)",
            "N2_Continuity_of_Principles": "ATTESTED (Act of faith is intrinsically free by nature)",
            "verdict_category": "CHANGED_CIVIL_JURISDICTION_APPLICATION_WITH_PRESERVED_MORAL_DUTY",
        },
    )
    n2106.add_thread(verse_ref="EXO.20.2-3", cluster_id="CL_FIRST_COMMANDMENT_MORAL_DUTY", warrant_mode="DIRECT_QUOTE", canon_scope="ECUMENICAL_66_SHARED", mediator="TRENT_CMD_I_DIGNITATIS_HUMANAE_1", newman_note="N6_CONSERVATIVE_ACTION", decibans=7.0)
    compiler.register_node(n2106)

    # 9 & 10. CCC §§ 2838 & 2842 — The Lord's Prayer: Forgiving Debts (Pillar IV: Christian Prayer)
    n2838 = LuaAssociativeNode(
        2838,
        pillar="IV_PRAYER",
        topic="Fifth Petition of the Our Father — 'Forgive Us Our Trespasses / Debts'",
        summary="In asking the Father to forgive our debts, we confess our insolvency before God's mercy and bind ourselves to forgive our neighbors.",
        trent_ref_id="TRENT_P4_PETITION5_DEBTS",
        vatican_en_url="https://www.vatican.va/archive/ENG0015/__PA6.HTM",
        vatican_lt_url="https://www.vatican.va/archive/catechismus_lt/p4s2a3_lt.htm",
        tradition_lenses={
            "catholic": "Trent Part IV (L18902–L18958) & CCC §§ 2838–2845: Divine mercy flows into human hearts only when they refuse to hoard ruthless debt collection against neighbors.",
            "lutheran": "Small Catechism Fifth Petition: Daily bilateral remission freeing the Christian to forgive neighbors gladly.",
            "reformed_carm": "100% Shared Core (Heidelberg Q&A 126 / Westminster Shorter Q. 105).",
            "skeptic_note": "Direct bridge to TWIFT's bilateral `Undo` / `Iqalah` floor: symmetric forgiveness breaks finite-horizon blood-feud defection.",
        },
        newman_profile={
            "N1_Preservation_of_Type": "ATTESTED (Identical across Didache 8, Trent Part IV, and CCC)",
            "N7_Chronic_Vigour": "ATTESTED (Athanasius observable mercy equilibrium)",
            "verdict_category": "EQUIVALENT_REAFFIRMED_UNIVERSAL_CHRISTIAN_PRAYER",
        },
    )
    n2842 = LuaAssociativeNode(
        2842,
        pillar="IV_PRAYER",
        topic="The 'As' of the Fifth Petition — Imitating Divine Mercy in Human Ledger Relations",
        summary="This 'as' is unique in Jesus' teaching: outpouring of divine mercy cannot penetrate a heart that closes itself to forgiving its debtor.",
        trent_ref_id="TRENT_P4_PETITION5_DEBTS",
        vatican_en_url="https://www.vatican.va/archive/ENG0015/__PA6.HTM",
        vatican_lt_url="https://www.vatican.va/archive/catechismus_lt/p4s2a3_lt.htm",
        tradition_lenses={
            "catholic": "CCC § 2842 + Parable of the Unmerciful Servant (Matt 18): Refusing mercy re-locks the ruthless 2D creditor prison.",
            "lutheran": "100% Shared Core: Neighbor-love is the spontaneous fruit of having our unpayable debt cancelled.",
            "reformed_carm": "100% Shared Core: Unforgiving spirit falsifies claim of regenerate trust.",
            "skeptic_note": "Demonstrates XCubes Top-Down Pericope Spreading (`S_W`) of `Matt 6:9–13` across `CCC §§ 2838 & 2842` without inflating cluster count!",
        },
        newman_profile={
            "N1_Preservation_of_Type": "ATTESTED",
            "N4_Logical_Sequence": "ATTESTED",
            "verdict_category": "EQUIVALENT_REAFFIRMED_UNIVERSAL_CHRISTIAN_PRAYER",
        },
    )
    n2842.add_thread(verse_ref="MAT.18.21-35", cluster_id="CL_UNMERCIFUL_SERVANT_PARABLE", warrant_mode="MORAL_EXEMPLAR", canon_scope="ECUMENICAL_66_SHARED", mediator="TRENT_PETITION_5", newman_note="N4_LOGICAL_SEQUENCE", decibans=8.2)
    compiler.register_node(n2838)
    compiler.register_node(n2842)

    # Demonstrate XCubes Top-Down Pericope Spreading (S_W) on Matt 6:9-13 across §§ 2838 & 2842
    compiler.spread_pericope(
        ccc_ids=[2838, 2842],
        verse_refs=["MAT.6.9-13"],
        cluster_id="CL_OUR_FATHER_PERICOPE",
        total_decibans=11.0,
        warrant_mode="PERICOPE_SPREAD",
        canon_scope="ECUMENICAL_66_SHARED",
        mediator="DIDACHE_8_TRENT_PART_IV",
        newman_note="N0_EXPLICIT_KERYGMA",
    )

    slab = compiler.compile_three_pass()
    resurrection_audit = build_resurrection_replicability_audit()
    cosmology_boundary = build_nicene_cosmology_boundary_matrix()

    bundle = {
        "project": "Epistemic Concordance — Scripture <-> Catechism of Trent (1566) <-> CCC (Bsar 6D XCube)",
        "license": "GNU-AGPLv3",
        "trent_witness_sha256": trent_sha,
        "xcube_slab": slab,
        "bible_public_domain": bible_store,
        "trent_public_domain": trent_passages,
        "resurrection_replicability_lab": resurrection_audit,
        "nicene_cosmology_boundary": cosmology_boundary,
        "outbound_ministry_directory": {
            "vatican_ccc_official": "https://www.vatican.va/archive/ENG0015/_INDEX.HTM",
            "usccb_print_and_licensed_ccc": "https://www.usccb.org/beliefs-and-teachings/what-we-believe/catechism/catechism-of-the-catholic-church",
            "lutheran_book_of_concord": "https://bookofconcord.org/",
            "reformed_carm_apologetics": "https://carm.org/",
        },
    }
    safety.assert_clean(bundle)
    bundle["bundle_sha256"] = canonical_sha256(bundle)
    return bundle


def build_nicene_cosmology_boundary_matrix() -> Dict[str, Any]:
    """
    4-Valued Carrollian Partition (`1` Nicene Attested | `?` Permissible Open Speculation | `0` Nicene Creed Contradiction)
    evaluating Mormon / American-Frontier Cosmology as a spirited 19th-century remix of Antiquity's philosophies.
    """
    return {
        "framing_note": (
            "Read as 19th-century American frontier literature, Mormon cosmology remixes several of Antiquity's boldest "
            "philosophical impulses—Stoic materialism, Platonic/Origenist pre-existence, Irenaean/Athanasian Theosis, "
            "and Renaissance cosmic plurality—with can-do homesteading optimism. Using Carroll's 4-valued lattice, we "
            "cleanly separate what ALL Nicene Christians (Catholic, Lutheran, and Reformed/CARM) rule out (`0`), what "
            "Nicene theology freely permits as open cosmic speculation (`?`), and what Nicene orthodoxy ALREADY affirms "
            "in cleaner Creator-preserving form (`1`)."
        ),
        "propositions": [
            {
                "id": "COSM_1_INHABITED_WORLDS",
                "state": EpistemicState.UNKNOWN_OPEN.value,
                "verdict_badge": "? PERMISSIBLE NICENE SPECULATION (Theologoumenon)",
                "frontier_motif": "Countless inhabited worlds across space ('worlds without number', Moses 1:33).",
                "antiquity_predecessor": "Cardinal Nicholas of Cusa (De Docta Ignorantia, 1440), Medieval Aristotelians after 1277, C.S. Lewis's Space Trilogy, Vatican Observatory.",
                "nicene_rule": "100% compatible with the Nicene Creed PROVIDED every world is created ex nihilo by the One Triune God (`Maker of heaven and earth, of all things visible and invisible`, CCC § 296) rather than spawned by contingent sky-ancestors.",
                "anchors": "Gen 1:1; Col 1:16; CCC §§ 290–296",
            },
            {
                "id": "COSM_2_PARTICIPATORY_THEOSIS",
                "state": EpistemicState.ATTESTED_ONE.value,
                "verdict_badge": "1 NICENE ATTESTED (Grace-By-Adoption, Never Species-Replacement)",
                "frontier_motif": "Human destiny as glorious cosmic co-heirs rather than passive harp-playing ghosts.",
                "antiquity_predecessor": "St. Irenaeus, St. Athanasius (De Incarnatione 54:3), 2 Peter 1:4 ('partakers of the divine nature').",
                "nicene_rule": "Nicene orthodoxy ALREADY affirms real glorification, cosmic co-reigning with Christ (Rom 8:19–21; Rev 22:5), and participatory Theosis by grace (CCC § 460)—while strictly forbidding erasing the uncreated Creator / finite creature distinction (Isa 43:10).",
                "anchors": "2 Pet 1:4; Rom 8:17–21; Isa 43:10; CCC § 460",
            },
            {
                "id": "COSM_3_EMBODIED_NEW_CREATION",
                "state": EpistemicState.ATTESTED_ONE.value,
                "verdict_badge": "1 NICENE ATTESTED (Physical Resurrection & Creative New Earth)",
                "frontier_motif": "Tangible, active, embodied eternal life building, exploring, and delighting in real matter.",
                "antiquity_predecessor": "Anti-Gnostic Patristics (Tertullian, Irenaeus, Augustine City of God Bk. XXII) vs. Platonic disembodied escapism.",
                "nicene_rule": "Gnosticism despised matter; the Nicene Creed ends with 'the resurrection of the body and the life of the world to come' (`Isa 65:17`, `Rev 21:24–26`, `Trent Art. XI`, `CCC §§ 1042–1050`). Creative embodied work & sub-creation in the New Creation is 100% orthodox!",
                "anchors": "1 Cor 15:42–44; Rom 8:21; Rev 21:24; CCC § 1047",
            },
            {
                "id": "COSM_4_UNEVALANGELIZED_HOPE",
                "state": EpistemicState.UNKNOWN_OPEN.value,
                "verdict_badge": "1 / ? NICENE MERCY FLOOR (Minus Proxy Ritual Mechanics)",
                "frontier_motif": "Refusal to believe unbaptized frontier family members who never heard the Gospel are damned by sheer geographic bad luck.",
                "antiquity_predecessor": "1 Peter 3:19 / 4:6 (Christ's proclamation to the dead), Justin Martyr, Roman Catechism Art. V, CCC §§ 633, 1260.",
                "nicene_rule": "Proxy baptisms for the dead (misreading Paul's ad-hominem in 1 Cor 15:29) are rejected (`0`), BUT the underlying moral instinct is already honored inside Nicene orthodoxy: God is not bound by His sacraments (CCC § 1257) and judges no one guilty for invincible ignorance.",
                "anchors": "1 Pet 3:19; Trent Art. V; CCC §§ 1257–1261",
            },
            {
                "id": "COSM_5_CONTINGENT_FATHER_INFINITE_REGRESS",
                "state": EpistemicState.EXCLUDED_ZERO.value,
                "verdict_badge": "0 HARD NICENE CONTRADICTION (Violates Divine Aseity & Monotheism)",
                "frontier_motif": "King Follett Discourse (1844): 'God himself was once as we are now, and is an exalted man' + corporeal Father of flesh and bone (D&C 130:22).",
                "antiquity_predecessor": "Stoic corporealism + Greco-Roman heroic apotheosis (Euhemerism).",
                "nicene_rule": "Directly contradicts Catholic, Lutheran, and Reformed/CARM orthodoxy (`One God, the Father Almighty`, `Before me there was no God formed, neither shall there be after me` [Isa 43:10], `God is spirit` [John 4:24], `I AM WHO I AM` [Exod 3:14]). An infinite regress of contingent planet-gods explains zero contingent existence.",
                "anchors": "Exod 3:14; Isa 43:10; John 4:24; CCC §§ 212, 253",
            },
            {
                "id": "COSM_6_PREMORTAL_SOULS_UNCREATED_MATTER",
                "state": EpistemicState.EXCLUDED_ZERO.value,
                "verdict_badge": "0 HARD NICENE CONTRADICTION (Violates Creatio ex Nihilo)",
                "frontier_motif": "Pre-mortal human intelligences co-eternal with God + creation as merely organizing pre-existing matter (Book of Abraham 3–4).",
                "antiquity_predecessor": "Plato's Timaeus (Demiurge shaping pre-existing chaos) + Origen's pre-existence of human souls (ruled out at Constantinople II, 553 AD).",
                "nicene_rule": "Nicene Christianity insists on Creatio ex Nihilo (`visible and invisible`, Col 1:16; Heb 11:3; 2 Macc 7:28; CCC §§ 296, 366): God is not a cosmic carpenter working inside a pre-existing universe—He is the transcendent Author of space, time, matter, and every individual soul.",
                "anchors": "Gen 1:1; John 1:3; Col 1:16; CCC §§ 296, 366",
            },
        ],
    }


HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Epistemic Concordance — Bible ↔ Catechism of Trent (1566) ↔ CCC (Bsar 6D XCube)</title>
<style>
  :root {
    --bg: #faf7f0;
    --paper: #fffdf9;
    --ink: #1b2220;
    --muted: #5a6460;
    --line: #d8d0c1;
    --pine: #1b4332;
    --gold: #9a6700;
    --burgundy: #7a2021;
    --navy: #1e3a5f;
    --violet: #4c1d95;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0;
    background: var(--bg);
    color: var(--ink);
    font-family: Georgia, "Iowan Old Style", "Palatino Linotype", serif;
    line-height: 1.55;
  }
  header {
    background: var(--pine);
    color: #f8f5ec;
    padding: 1.4rem 1.5rem;
    border-bottom: 4px solid var(--gold);
  }
  header h1 { margin: 0 0 .35rem 0; font-size: 1.45rem; letter-spacing: .01em; }
  header p { margin: 0; font-size: .94rem; color: #d8f3dc; font-family: system-ui, -apple-system, sans-serif; }
  .pill-row { display: flex; flex-wrap: wrap; gap: .45rem; margin-top: .7rem; font-family: system-ui, sans-serif; font-size: .78rem; }
  .pill { background: rgba(255,255,255,.13); padding: .22rem .6rem; border-radius: 999px; border: 1px solid rgba(255,255,255,.24); }
  main { max-width: 1240px; margin: 0 auto; padding: 1.25rem; }
  .tabs { display: flex; flex-wrap: wrap; gap: .5rem; margin-bottom: 1.1rem; font-family: system-ui, sans-serif; }
  .tab-btn {
    border: 1px solid var(--line);
    background: var(--paper);
    color: var(--ink);
    padding: .55rem 1rem;
    border-radius: 6px;
    font-weight: 700;
    cursor: pointer;
    font-size: .9rem;
  }
  .tab-btn.active { background: var(--pine); color: #fff; border-color: var(--pine); }
  .panel { display: none; }
  .panel.active { display: block; }
  .controls {
    background: var(--paper);
    border: 1px solid var(--line);
    border-radius: 8px;
    padding: .9rem 1rem;
    margin-bottom: 1rem;
    display: flex;
    flex-wrap: wrap;
    gap: .85rem;
    align-items: center;
    font-family: system-ui, sans-serif;
    font-size: .86rem;
  }
  select, input[type="range"] { padding: .35rem .5rem; border: 1px solid var(--line); border-radius: 5px; background: #fff; }
  .grid-2 { display: grid; grid-template-columns: 340px 1fr; gap: 1rem; }
  @media (max-width: 900px) { .grid-2 { grid-template-columns: 1fr; } }
  .sidebar-list { display: flex; flex-direction: column; gap: .45rem; }
  .node-item {
    text-align: left;
    background: var(--paper);
    border: 1px solid var(--line);
    border-left: 4px solid var(--pine);
    border-radius: 6px;
    padding: .65rem .8rem;
    cursor: pointer;
    font-family: system-ui, sans-serif;
  }
  .node-item.active { background: #edf6f0; border-color: var(--pine); box-shadow: 0 1px 4px rgba(0,0,0,.06); }
  .node-item strong { display: block; font-size: .92rem; color: var(--pine); }
  .node-item small { color: var(--muted); font-size: .78rem; }
  .card {
    background: var(--paper);
    border: 1px solid var(--line);
    border-radius: 8px;
    padding: 1.1rem 1.25rem;
    margin-bottom: 1rem;
  }
  .card h2, .card h3 { margin-top: 0; }
  .badge {
    display: inline-block;
    padding: .16rem .5rem;
    border-radius: 4px;
    font-family: system-ui, sans-serif;
    font-size: .74rem;
    font-weight: 700;
    margin-right: .35rem;
  }
  .b-shared { background: #d8f3dc; color: #1b4332; }
  .b-deut { background: #fef3c7; color: #92400e; }
  .b-db { background: #e0e7ff; color: #1e3a8a; }
  .b-spread { background: #f3e8ff; color: #581c87; }
  .verse-box {
    border-left: 3px solid var(--gold);
    background: #fcfaf4;
    padding: .7rem .95rem;
    margin: .65rem 0;
    border-radius: 0 6px 6px 0;
  }
  .trent-box {
    border-left: 4px solid var(--burgundy);
    background: #fdf8f6;
    padding: .85rem 1rem;
    border-radius: 0 6px 6px 0;
    white-space: pre-wrap;
    font-size: .92rem;
    max-height: 290px;
    overflow-y: auto;
  }
  .lenses { display: grid; grid-template-columns: repeat(auto-fit, minmax(230px, 1fr)); gap: .75rem; margin-top: .75rem; font-family: system-ui, sans-serif; font-size: .84rem; }
  .lens-card { border: 1px solid var(--line); border-radius: 6px; padding: .7rem .85rem; background: #fff; }
  .out-links { display: flex; flex-wrap: wrap; gap: .5rem; margin-top: .75rem; font-family: system-ui, sans-serif; }
  .btn-link {
    display: inline-block;
    padding: .38rem .75rem;
    border-radius: 5px;
    text-decoration: none;
    font-size: .8rem;
    font-weight: 700;
    color: #fff;
    background: var(--pine);
  }
  .btn-link.alt { background: var(--burgundy); }
  .btn-link.carm { background: var(--navy); }
  .btn-link.luth { background: var(--gold); }
  pre.code {
    background: #1b2220;
    color: #d8f3dc;
    padding: .9rem 1rem;
    border-radius: 6px;
    overflow-x: auto;
    font-family: ui-monospace, SFMono-Regular, Consolas, monospace;
    font-size: .82rem;
  }
  table { width: 100%; border-collapse: collapse; font-family: system-ui, sans-serif; font-size: .84rem; }
  th, td { border-bottom: 1px solid var(--line); padding: .55rem .5rem; text-align: left; vertical-align: top; }
  th { background: #f3efe4; font-weight: 700; }
  footer {
    max-width: 1240px;
    margin: 1.5rem auto 2.5rem auto;
    padding: 0 1.25rem;
    font-family: system-ui, sans-serif;
    font-size: .8rem;
    color: var(--muted);
  }
</style>
</head>
<body>
<header>
  <h1>Epistemic Concordance: Scripture ↔ Catechism of Trent (1566) ↔ CCC</h1>
  <p>Powered by <strong>Bsar 6D XCube</strong> (Asar 3-Pass Slab + R Pipe Verbs + Lua Dynamic Frames + CarrollCube ∃m) · Cardinal Newman 7-Note Profiles · Psychometric Replicability Engine</p>
  <div class="pill-row">
    <span class="pill" id="meta-rats">RATS SHA-256: loading…</span>
    <span class="pill">Trent 1566 Witness: Public Domain (Byte-Pinned)</span>
    <span class="pill">Scripture: Douay-Rheims 1899 &amp; KJV 1769 (Public Domain)</span>
    <span class="pill">License: GNU AGPLv3 (Free Open Hosting · Dual-License Commercial Ready)</span>
  </div>
</header>

<main>
  <div class="tabs">
    <button class="tab-btn active" onclick="switchTab('ccc')">1. CCC Statement → Bible &amp; Trent (Forward CSR)</button>
    <button class="tab-btn" onclick="switchTab('verse')">2. Bible Verse → All Supporting CCC §§ (Reverse CSC)</button>
    <button class="tab-btn" onclick="switchTab('rpipe')">3. Live R-Verb XCube Slicer (|&gt;)</button>
    <button class="tab-btn" onclick="switchTab('hume')">4. Hume “Of Miracles” (@PAHoyeck) Replicability Lab</button>
    <button class="tab-btn" onclick="switchTab('cosm')">5. Nicene Cosmology Boundary: LDS &amp; Antiquity (1 / ? / 0)</button>
  </div>

  <!-- TAB 1: CCC -> BIBLE & TRENT -->
  <section id="panel-ccc" class="panel active">
    <div class="controls">
      <label><strong>Bible Translation:</strong>
        <select id="bible-ver" onchange="renderActiveCCC()">
          <option value="drb">Douay-Rheims 1899 (73-Book Catholic PD)</option>
          <option value="kjv">King James Version 1769 (66-Book + Apocrypha PD)</option>
        </select>
      </label>
      <label><strong>Canon Filter:</strong>
        <select id="canon-filter" onchange="renderActiveCCC()">
          <option value="ALL">All 73 Books (Full Catholic Canon)</option>
          <option value="ECUMENICAL_66_SHARED">66-Book Shared Canon Only (Lutheran / Reformed / CARM Intersection)</option>
        </select>
      </label>
      <label>
        <input type="checkbox" id="eliminate-mediator" onchange="renderActiveCCC()">
        <strong>CarrollCube Middle-Term Projection (∃m):</strong> Collapse mediators into direct CCC ↔ Verse view
      </label>
    </div>

    <div class="grid-2">
      <div class="sidebar-list" id="ccc-sidebar"></div>
      <div id="ccc-detail"></div>
    </div>
  </section>

  <!-- TAB 2: REVERSE VERSE -> CCC -->
  <section id="panel-verse" class="panel">
    <div class="controls">
      <label><strong>Select Any Scripture Locus:</strong>
        <select id="verse-selector" onchange="renderReverseVerse()"></select>
      </label>
      <span style="color:var(--muted)">Instant O(1) lookup via Bsar Reverse CSC Index (`reverse_verse_to_edge_ids`)</span>
    </div>
    <div id="verse-detail"></div>
  </section>

  <!-- TAB 3: LIVE R-VERB XCUBE SLICER -->
  <section id="panel-rpipe" class="panel">
    <div class="card">
      <h3>Interactive <code>Bsar</code> R-Verb Hypercube Pipeline (Copy-on-Modify)</h3>
      <div class="controls" style="margin-top:.5rem">
        <label><strong><code>filter(pillar == …)</code></strong>
          <select id="r-pillar" onchange="runRPipe()">
            <option value="ALL">* (All 4 Pillars)</option>
            <option value="I_CREED">I_CREED</option>
            <option value="II_SACRAMENTS">II_SACRAMENTS</option>
            <option value="III_LIFE_IN_CHRIST">III_LIFE_IN_CHRIST</option>
            <option value="IV_PRAYER">IV_PRAYER</option>
          </select>
        </label>
        <label><strong><code>filter(canon_scope == …)</code></strong>
          <select id="r-canon" onchange="runRPipe()">
            <option value="ALL">* (73-Book All)</option>
            <option value="ECUMENICAL_66_SHARED">ECUMENICAL_66_SHARED (66-Book Core)</option>
            <option value="DEUTEROCANON_7_BOOKS">DEUTEROCANON_7_BOOKS</option>
          </select>
        </label>
        <label><strong><code>rollup_slice(by = …)</code></strong>
          <select id="r-group" onchange="runRPipe()">
            <option value="ccc_id">CCC Paragraph (Newman Cable Strength)</option>
            <option value="pillar">4 Catechism Pillars</option>
            <option value="newman_note">Cardinal Newman 7 Notes</option>
          </select>
        </label>
      </div>
      <pre class="code" id="r-code-preview"></pre>
      <div id="r-table-out"></div>
    </div>
  </section>

  <!-- TAB 4: HUME OF MIRACLES REPLICABILITY LAB -->
  <section id="panel-hume" class="panel">
    <div class="card">
      <h2>Psychometric Replicability Testimony vs. Hume's <em>Of Miracles</em> (<code>@PAHoyeck</code> Audit)</h2>
      <p id="hume-intro" style="color:var(--muted)"></p>
      <div class="controls">
        <label><strong>Skeptical Starting Prior <code>P(Resurrection)</code>:</strong>
          <input type="range" id="hume-prior-log" min="-6" max="-0.3" step="0.1" value="-3.0" oninput="renderHumeLab()">
          <span id="hume-prior-label" style="font-weight:700;color:var(--burgundy)"></span>
        </label>
        <label><strong>Post-Hoc Naturalistic <code>HARKing</code> Patches (<code>Δk</code>):</strong>
          <select id="hume-patches" onchange="renderHumeLab()">
            <option value="0">0 Patches — Single Coherent Naturalistic Mechanism (Honest Skeptic)</option>
            <option value="2">2 Patches — Grief Hallucination + Separate Wrong-Tomb Excuse (-10 dB MDL)</option>
            <option value="3" selected>3 Patches — Hallucination + Hostile Paul Seizure + Stolen/Wrong Tomb (-15 dB MDL)</option>
            <option value="4">4 Patches — Swoon + Conspiracy + Mass Hallucination + Paul Seizure (-20 dB MDL)</option>
          </select>
        </label>
      </div>
      <div id="hume-scoreboard"></div>
      <div id="hume-channels"></div>
    </div>
  </section>

  <!-- TAB 5: NICENE COSMOLOGY BOUNDARY (FRONTIER LDS & ANTIQUITY REMIXES) -->
  <section id="panel-cosm" class="panel">
    <div class="card">
      <h2>Nicene Creed Cosmology Boundary: American-Frontier LDS Literature &amp; Antiquity's Philosophies</h2>
      <p id="cosm-intro" style="color:var(--muted)"></p>
      <div class="controls">
        <label><strong>Filter by Carrollian 4-Valued Epistemic State:</strong>
          <select id="cosm-filter" onchange="renderCosmologyLab()">
            <option value="ALL">Show All (1 Attested · ? Permissible Speculation · 0 Nicene Contradiction)</option>
            <option value="SAFE_OR_ATTESTED">Acceptable to Theorize / Affirm Inside Nicene Orthodoxy (1 &amp; ?)</option>
            <option value="0">Incompatible with Nicene Creed (0 — Catholic, Lutheran &amp; CARM Agreed)</option>
          </select>
        </label>
      </div>
      <div id="cosm-cards"></div>
    </div>
  </section>
</main>

<footer>
  <strong>Respectful Concordance &amp; Fair Revenue Architecture:</strong> Verbatim Bible texts (Douay-Rheims 1899 &amp; KJV 1769) and the 1566 Roman Catechism of Trent are in the Public Domain. Modern CCC paragraphs are indexed by uncopyrightable factual citation coordinates paired with original 1-sentence summaries and direct outbound links to <a href="https://www.vatican.va/archive/ENG0015/_INDEX.HTM" target="_blank" rel="noopener">Vatican.va</a>, <a href="https://www.usccb.org/beliefs-and-teachings/what-we-believe/catechism/catechism-of-the-catholic-church" target="_blank" rel="noopener">USCCB Official Print/Licensed Editions</a>, <a href="https://bookofconcord.org/" target="_blank" rel="noopener">BookOfConcord.org</a>, and <a href="https://carm.org/" target="_blank" rel="noopener">CARM.org</a>. Licensed under <strong>GNU AGPLv3</strong>; commercial publishers holding official CCC prose licenses can hydrate inline text via <code>LicensedTextAdapter</code> under a commercial partnership.
</footer>

<script>
const BUNDLE = __BUNDLE_JSON__;
let currentCCC = "604";

function switchTab(name) {
  document.querySelectorAll('.tabs .tab-btn').forEach((b, idx) => {
    const map = ['ccc', 'verse', 'rpipe', 'hume', 'cosm'];
    b.classList.toggle('active', map[idx] === name);
  });
  document.querySelectorAll('.panel').forEach(p => p.classList.remove('active'));
  document.getElementById('panel-' + name).classList.add('active');
}

function initApp() {
  const slab = BUNDLE.xcube_slab;
  document.getElementById('meta-rats').textContent =
    `Bsar Slab SHA-256: ${slab.rats_sha256.slice(0, 16)}… (${slab.counts.ccc_nodes} Nodes · ${slab.counts.sparse_edges} Hilbert Edges)`;

  const sidebar = document.getElementById('ccc-sidebar');
  const nodeIds = Object.keys(slab.nodes).sort((a, b) => Number(a) - Number(b));
  sidebar.innerHTML = nodeIds.map(id => {
    const n = slab.nodes[id];
    return `<button class="node-item ${id === currentCCC ? 'active' : ''}" id="nav-ccc-${id}" onclick="selectCCC('${id}')">
      <strong>CCC § ${id} — ${escapeHtml(n.topic)}</strong>
      <small>${escapeHtml(n.pillar)}</small>
    </button>`;
  }).join('');

  const vSel = document.getElementById('verse-selector');
  const vKeys = Object.keys(slab.reverse_verse_to_edge_ids).sort();
  vSel.innerHTML = vKeys.map(vk => {
    const b = BUNDLE.bible_public_domain[vk] || { ref: vk, canon: '' };
    return `<option value="${vk}" ${vk === 'JHN.3.16' ? 'selected' : ''}>${escapeHtml(b.ref)} [${vk}] (${escapeHtml(b.canon)})</option>`;
  }).join('');

  renderActiveCCC();
  renderReverseVerse();
  runRPipe();
  renderHumeLab();
  renderCosmologyLab();
}

function escapeHtml(s) {
  return String(s || '').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
}

function selectCCC(id) {
  currentCCC = String(id);
  document.querySelectorAll('.node-item').forEach(el => el.classList.remove('active'));
  const btn = document.getElementById('nav-ccc-' + currentCCC);
  if (btn) btn.classList.add('active');
  renderActiveCCC();
}

function computeDeduplicatedCableDb(edges) {
  const clusters = {};
  edges.forEach(e => {
    const cid = e.cluster_id;
    clusters[cid] = Math.max(clusters[cid] ?? -32768, e.db_q8_8);
  });
  const sumQ8 = Object.values(clusters).reduce((a, b) => a + b, 0);
  return {
    decibans: (sumQ8 / 256.0).toFixed(2),
    clusterCount: Object.keys(clusters).length
  };
}

function renderActiveCCC() {
  const slab = BUNDLE.xcube_slab;
  const node = slab.nodes[currentCCC];
  const ver = document.getElementById('bible-ver').value;
  const canonFilter = document.getElementById('canon-filter').value;
  const elimMed = document.getElementById('eliminate-mediator').checked;

  let edges = (slab.forward_ccc_to_edge_ids[currentCCC] || []).map(i => slab.edges[i]);
  if (canonFilter !== 'ALL') {
    edges = edges.filter(e => e.canon_scope === canonFilter);
  }

  if (elimMed) {
    const byVerse = {};
    edges.forEach(e => {
      if (!byVerse[e.verse_ref]) {
        byVerse[e.verse_ref] = { ...e, mediator: '* (∃m Projected)', mediators_list: [e.mediator] };
      } else {
        byVerse[e.verse_ref].mediators_list.push(e.mediator);
        byVerse[e.verse_ref].db_q8_8 = Math.max(byVerse[e.verse_ref].db_q8_8, e.db_q8_8);
      }
    });
    edges = Object.values(byVerse);
  }

  const cable = computeDeduplicatedCableDb(edges);
  const trent = BUNDLE.trent_public_domain[node.trent_ref_id];

  const versesHtml = edges.length === 0
    ? `<p style="color:var(--burgundy)"><strong>0 edges under current Canon filter!</strong> (Switch Canon Filter back to 73-Book to see Deuterocanonical witnesses.)</p>`
    : edges.map(e => {
        const b = BUNDLE.bible_public_domain[e.verse_ref] || { ref: e.verse_ref, drb: '', kjv: '', canon: e.canon_scope };
        const canonBadge = b.canon === 'ECUMENICAL_66_SHARED'
          ? `<span class="badge b-shared">66-Book Shared Core</span>`
          : `<span class="badge b-deut">7-Book Deuterocanon</span>`;
        const spreadBadge = e.is_spread_from_pericope
          ? `<span class="badge b-spread">XCubes Spread (S_W)</span>` : '';
        const medLabel = elimMed
          ? `<code>∃m</code> Projected (click to note hidden mediators: ${escapeHtml((e.mediators_list || []).join(', '))})`
          : `Mediator: <code>${escapeHtml(e.mediator)}</code>`;
        return `<div class="verse-box">
          <div>
            <strong>${escapeHtml(b.ref)}</strong>
            ${canonBadge}
            <span class="badge b-db">+${(e.db_q8_8 / 256.0).toFixed(2)} dB (Q8.8: ${e.db_q8_8})</span>
            ${spreadBadge}
          </div>
          <p style="margin:.4rem 0">"${escapeHtml(b[ver])}"</p>
          <small style="color:var(--muted);font-family:system-ui,sans-serif">
            Cluster: <code>${escapeHtml(e.cluster_id)}</code> · Mode: <code>${escapeHtml(e.warrant_mode)}</code> · Newman: <code>${escapeHtml(e.newman_note)}</code> · ${medLabel}
          </small>
        </div>`;
      }).join('');

  const newmanRows = Object.entries(node.newman_profile || {}).map(([k, v]) =>
    `<tr><td><code>${escapeHtml(k)}</code></td><td>${escapeHtml(v)}</td></tr>`
  ).join('');

  const L = node.tradition_lenses || {};
  document.getElementById('ccc-detail').innerHTML = `
    <div class="card">
      <span class="badge b-db">Newman Convergent Cable: +${cable.decibans} dB (${cable.clusterCount} Independent Clusters from ${edges.length} Edges)</span>
      <h2 style="margin:.45rem 0 .25rem 0">CCC § ${node.ccc_id} — ${escapeHtml(node.topic)}</h2>
      <p style="margin:.3rem 0"><strong>Clean-Room Atomic Proposition:</strong> ${escapeHtml(node.clean_room_proposition)}</p>
      <div class="out-links">
        <a class="btn-link" href="${escapeHtml(node.vatican_en_url)}" target="_blank" rel="noopener">Read Verbatim on Vatican.va (EN) ↗</a>
        <a class="btn-link alt" href="${escapeHtml(node.vatican_latin_url)}" target="_blank" rel="noopener">Normative Latin Editio Typica ↗</a>
        <a class="btn-link luth" href="${escapeHtml(node.official_print_and_flipbook_url)}" target="_blank" rel="noopener">Official USCCB Flipbook / Buy Print ↗</a>
      </div>
    </div>

    <div class="card">
      <h3>Supporting Scripture Strands (${ver === 'drb' ? 'Douay-Rheims 1899' : 'King James Version 1769'} — Public Domain)</h3>
      ${versesHtml}
    </div>

    <div class="card">
      <h3>Cross-Referenced 1566 Catechism of the Council of Trent (Public Domain · Byte-Pinned)</h3>
      <p style="margin:0 0 .45rem 0;font-family:system-ui,sans-serif;font-size:.82rem;color:var(--muted)">
        <strong>${escapeHtml(trent.title)}</strong> · Pin: <code>${escapeHtml(trent.line_range)}</code> in <code>rc-en.txt</code> (SHA-256: <code>${trent.source_sha256.slice(0, 14)}…</code>)<br>
        <em>Note: ${escapeHtml(trent.editorial_warning)}</em>
      </p>
      <div class="trent-box">${escapeHtml(trent.verbatim_text)}</div>
    </div>

    <div class="card">
      <h3>Four-Way Honest Theological &amp; Epistemic Lens (Zero Straw-Men)</h3>
      <div class="lenses">
        <div class="lens-card"><strong>Catholic (Trent 1566 → CCC)</strong><p>${escapeHtml(L.catholic)}</p></div>
        <div class="lens-card"><strong>Lutheran (Concord / John 3:16)</strong><p>${escapeHtml(L.lutheran)}</p><a href="https://bookofconcord.org/" target="_blank" rel="noopener">BookOfConcord.org ↗</a></div>
        <div class="lens-card"><strong>Reformed / CARM (66-Book Core)</strong><p>${escapeHtml(L.reformed_carm)}</p><a href="https://carm.org/" target="_blank" rel="noopener">CARM.org Reference ↗</a></div>
        <div class="lens-card"><strong>Epistemic / Skeptic Audit</strong><p>${escapeHtml(L.skeptic_note)}</p></div>
      </div>
      <h4 style="margin:1rem 0 .4rem 0;font-family:system-ui,sans-serif">Cardinal Newman Non-Collapsed Profile (Hermes Synoptics Protocol)</h4>
      <table><tbody>${newmanRows}</tbody></table>
    </div>
  `;
}

function renderReverseVerse() {
  const vk = document.getElementById('verse-selector').value;
  const slab = BUNDLE.xcube_slab;
  const b = BUNDLE.bible_public_domain[vk];
  const edgeIds = slab.reverse_verse_to_edge_ids[vk] || [];
  const edges = edgeIds.map(i => slab.edges[i]);

  const cards = edges.map(e => {
    const n = slab.nodes[String(e.ccc_id)];
    const t = BUNDLE.trent_public_domain[n.trent_ref_id];
    return `<div class="card">
      <span class="badge b-db">CCC § ${n.ccc_id}</span>
      <span class="badge b-shared">${escapeHtml(e.warrant_mode)} (+${(e.db_q8_8/256).toFixed(2)} dB)</span>
      <h3 style="margin:.4rem 0">${escapeHtml(n.topic)}</h3>
      <p>${escapeHtml(n.clean_room_proposition)}</p>
      <p style="font-family:system-ui,sans-serif;font-size:.83rem;color:var(--muted)">
        <strong>1566 Catechism of Trent Parallel:</strong> ${escapeHtml(t.title)} (<code>${escapeHtml(t.line_range)}</code>) · Mediator: <code>${escapeHtml(e.mediator)}</code>
      </p>
      <button class="tab-btn" onclick="selectCCC('${n.ccc_id}');switchTab('ccc')">Inspect Full CCC § ${n.ccc_id} + Trent Dossier →</button>
    </div>`;
  }).join('');

  document.getElementById('verse-detail').innerHTML = `
    <div class="card">
      <h2>${escapeHtml(b.ref)} <span class="badge ${b.canon === 'ECUMENICAL_66_SHARED' ? 'b-shared' : 'b-deut'}">${escapeHtml(b.canon)}</span></h2>
      <p><strong>Douay-Rheims (1899):</strong> "${escapeHtml(b.drb)}"</p>
      <p><strong>King James (1769):</strong> "${escapeHtml(b.kjv)}"</p>
    </div>
    <h3>Supported Catechism Statements (${edges.length} Hilbert-Indexed Edges)</h3>
    ${cards}
  `;
}

function runRPipe() {
  const p = document.getElementById('r-pillar').value;
  const c = document.getElementById('r-canon').value;
  const g = document.getElementById('r-group').value;

  const filters = [];
  if (p !== 'ALL') filters.push(`pillar == "${p}"`);
  if (c !== 'ALL') filters.push(`canon_scope == "${c}"`);
  const filterCode = filters.length ? `\n  filter(${filters.join(', ')}) |>` : '';

  document.getElementById('r-code-preview').textContent =
`ccc_trent_xcube |> ${filterCode}
  inner_join(bible_pd, by = "verse_ref") |>
  rollup_slice(
    axes = c("${g}"),
    agg  = newman_cable_q8_8(dedup_by = "cluster_id")
  ) |>
  select(${g}, raw_edges, independent_clusters, cable_decibans, verses)`;

  let rows = BUNDLE.xcube_slab.edges.slice();
  if (p !== 'ALL') rows = rows.filter(r => r.pillar === p);
  if (c !== 'ALL') rows = rows.filter(r => r.canon_scope === c);

  const buckets = {};
  rows.forEach(r => {
    const key = String(r[g]);
    if (!buckets[key]) buckets[key] = [];
    buckets[key].push(r);
  });

  const trs = Object.keys(buckets).sort().map(k => {
    const items = buckets[k];
    const cab = computeDeduplicatedCableDb(items);
    const verses = [...new Set(items.map(x => x.verse_ref))].join(', ');
    const label = g === 'ccc_id' ? `CCC § ${k} (${BUNDLE.xcube_slab.nodes[k].topic})` : k;
    return `<tr>
      <td><strong>${escapeHtml(label)}</strong></td>
      <td>${items.length}</td>
      <td>${cab.clusterCount}</td>
      <td><strong>+${cab.decibans} dB</strong></td>
      <td><code>${escapeHtml(verses)}</code></td>
    </tr>`;
  }).join('');

  document.getElementById('r-table-out').innerHTML = `
    <table>
      <thead><tr><th>Slice Key (<code>${escapeHtml(g)}</code>)</th><th>Raw Edges</th><th>Deduplicated Clusters</th><th>Newman Cable (Q8.8 dB)</th><th>Supporting Scripture Verses</th></tr></thead>
      <tbody>${trs}</tbody>
    </table>`;
}

function renderHumeLab() {
  const lab = BUNDLE.resurrection_replicability_lab;
  document.getElementById('hume-intro').textContent = lab.hoyeck_hume_note;

  const logPrior = parseFloat(document.getElementById('hume-prior-log').value);
  const p0 = Math.pow(10, logPrior);
  const patches = parseInt(document.getElementById('hume-patches').value, 10);

  const priorDb = 10 * Math.log10(p0 / (1 - p0));
  const base = lab.clean_single_mechanism_skeptic;
  const cableDb = base.empirical_cable_decibans;
  const mdlDb = 5.0 * patches;
  const postDb = priorDb + cableDb + mdlDb;
  const postOdds = Math.pow(10, postDb / 10.0);
  const postProb = postOdds / (1 + postOdds);

  document.getElementById('hume-prior-label').textContent =
    `P(H) = ${(p0 * 100).toFixed(4)}% (${priorDb.toFixed(1)} dB)`;

  document.getElementById('hume-scoreboard').innerHTML = `
    <div class="lenses" style="margin-bottom:1rem">
      <div class="lens-card">
        <strong>1. Humean Prior (<code>t = 0</code>)</strong>
        <div style="font-size:1.35rem;font-weight:800;color:var(--burgundy)">${priorDb.toFixed(2)} dB</div>
        <small>Cromwell-bounded starting skepticism</small>
      </div>
      <div class="lens-card">
        <strong>2. Deduplicated Witness Cable</strong>
        <div style="font-size:1.35rem;font-weight:800;color:var(--pine)">+${cableDb.toFixed(2)} dB</div>
        <small>${base.independent_cluster_count} independent clusters (${base.pseudoreplication_blocked.length} Synoptic duplicate auto-collapsed!)</small>
      </div>
      <div class="lens-card">
        <strong>3. Anti-HARKing MDL Adjustment</strong>
        <div style="font-size:1.35rem;font-weight:800;color:var(--violet)">+${mdlDb.toFixed(2)} dB</div>
        <small>${patches} post-hoc naturalistic rescue epicycles penalized at 5 dB/patch</small>
      </div>
      <div class="lens-card">
        <strong>4. Posterior Probability</strong>
        <div style="font-size:1.35rem;font-weight:800;color:var(--pine)">${(postProb * 100).toFixed(3)}% (${postDb >= 0 ? '+' : ''}${postDb.toFixed(2)} dB)</div>
        <small>Rubric SHA-256 locked: <code>${base.rubric_sha256.slice(0, 12)}…</code></small>
      </div>
    </div>
  `;

  const chRows = base.cluster_breakdown.map(c => `
    <tr>
      <td><strong>${escapeHtml(c.title)}</strong><br><small>Merged parallels: <code>${escapeHtml(c.merged_parallels.join(', '))}</code></small></td>
      <td><code>${escapeHtml(c.locus)}</code></td>
      <td><span class="badge b-shared">${escapeHtml(c.incentive_profile)}</span></td>
      <td><strong>+${c.decibans.toFixed(2)} dB</strong></td>
    </tr>
  `).join('');

  document.getElementById('hume-channels').innerHTML = `
    <h3>Pre-Registered Independent Evidentiary Clusters (Pseudo-Replication Blocked)</h3>
    <table>
      <thead><tr><th>Independent Cluster</th><th>Primary Sources</th><th>Psychometric Incentive Filter</th><th>Weight (Q8.8 dB)</th></tr></thead>
      <tbody>${chRows}</tbody>
    </table>
  `;
}

function renderCosmologyLab() {
  const cosm = BUNDLE.nicene_cosmology_boundary;
  document.getElementById('cosm-intro').textContent = cosm.framing_note;
  const f = document.getElementById('cosm-filter').value;

  let items = cosm.propositions.slice();
  if (f === 'SAFE_OR_ATTESTED') {
    items = items.filter(p => p.state === '1' || p.state === '?');
  } else if (f === '0') {
    items = items.filter(p => p.state === '0');
  }

  document.getElementById('cosm-cards').innerHTML = items.map(p => {
    const badgeClass = p.state === '1' ? 'b-shared' : (p.state === '?' ? 'b-db' : 'b-deut');
    const borderCol = p.state === '0' ? 'var(--burgundy)' : (p.state === '1' ? 'var(--pine)' : 'var(--navy)');
    return `<div class="card" style="border-left:5px solid ${borderCol}">
      <span class="badge ${badgeClass}">${escapeHtml(p.verdict_badge)}</span>
      <h3 style="margin:.45rem 0">${escapeHtml(p.frontier_motif)}</h3>
      <p style="margin:.35rem 0"><strong>Antiquity / Classical Predecessor:</strong> ${escapeHtml(p.antiquity_predecessor)}</p>
      <p style="margin:.35rem 0"><strong>Nicene Creed &amp; Scripture Razor:</strong> ${escapeHtml(p.nicene_rule)}</p>
      <small style="color:var(--muted);font-family:system-ui,sans-serif"><strong>Primary Anchors:</strong> <code>${escapeHtml(p.anchors)}</code></small>
    </div>`;
  }).join('');
}

initApp();
</script>
</body>
</html>
"""


def write_static_build(out_dir: Path) -> Dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    bundle = build_concordance_bundle()
    json_path = out_dir / "ccc_trent_bible_xcube.json"
    html_path = out_dir / "index.html"

    json_bytes = json.dumps(bundle, indent=2, ensure_ascii=False).encode("utf-8")
    json_path.write_bytes(json_bytes)

    compact_json = json.dumps(bundle, ensure_ascii=False).replace("</", "<\\/")
    html_text = HTML_TEMPLATE.replace("__BUNDLE_JSON__", compact_json)
    html_path.write_text(html_text, encoding="utf-8")

    return {
        "json_path": str(json_path),
        "json_bytes": len(json_bytes),
        "html_path": str(html_path),
        "html_bytes": html_path.stat().st_size,
        "rats_sha256": bundle["xcube_slab"]["rats_sha256"],
        "bundle_sha256": bundle["bundle_sha256"],
    }


if __name__ == "__main__":
    dist = Path(__file__).resolve().parent / "dist"
    stats = write_static_build(dist)
    print(json.dumps(stats, indent=2))
