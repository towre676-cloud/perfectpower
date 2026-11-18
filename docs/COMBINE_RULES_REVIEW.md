# Direct inspection of the NFL Big Data Bowl 2027 Rules tab

Inspected 4 November 2026 at the rendered [official Rules tab](https://www.kaggle.com/competitions/nfl-big-data-bowl-2027/rules). The page was read in the browser, including Competition-Specific Terms, Competition-Specific Rules and General Competition Rules through Definitions. The extraction service encountered a CSS loading error; the browser rendered the full rules successfully. No Join, entry, agreement-acceptance or submission action was taken.

| Topic | Directly observed rule | Consequence for this package |
| --- | --- | --- |
| Hackathon submissions | Competition-Specific Rules §2 allows one submission per hackathon team; the general daily/final-submission numbers are superseded for this format | Prepare one final entry; drafts and notebook publication are separate from submitting it |
| Teams | Competition-Specific Rules §1 caps teams at five; pre-merger hackathon submissions are unsubmitted when teams merge | Confirm the actual team roster before entry; no roster is inferred here |
| Data license and use | Specific Terms §7 names CC BY-NC 4.0; Specific Rules §4 restricts data use to noncommercial purposes and requires protecting access from nonparticipants | Continue excluding official rows, extracted private tables and per-player forecasts from public artifacts |
| Private sharing | General Rules §§5–6 prohibit private sharing of competition code/data between teams | Do not distribute the private continuation or research code to other teams privately |
| Public code | General Rules §6 requires public competition-code sharing through the competition-associated Kaggle forum or notebooks, under an OSI-approved license allowing commercial code use | The self-contained public Kaggle notebook is still needed; a GitHub link alone does not fulfill this channel requirement |
| Winning solution | Specific Rules §5 requires an OSI-approved license without commercial-use limits for winning submission/code, with stated exceptions for input data and certain third-party software/models | Keep code and input-data licenses distinct; retain license/attribution notices and prepare an explicit winning-submission license grant if applicable |
| External data/tools | Specific Rules §6 allows external resources subject to accessibility and the host's reasonableness/minimal-cost criteria; licensed AutoML tools are allowed | This entry needs no paid proprietary data or LLM at inference; disclose methodology and software, without asserting a blanket tool exemption |
| Reproduction | Specific Rules §§5 and 8 require reproducible methodology and may require final code/environment details | Preserve pinned inputs, estimator code, receipts and explicit fresh-versus-historical execution status |
| Eligibility | Specific Rules §7 and General Rules §1 set age, account, sanctions, affiliation and representation conditions | Individual eligibility is not certified by inspecting the research files |
| Acceptance | Entry/submission accepts binding rules | Viewing the rules did not accept them or authorize entry/submission |

The overview separately sets the 2,000-word/fewer-than-10-table-or-figure limits, required public notebook and Combine-to-NFL linkage. The deadline remains the Timeline page's 6 January 2027, 23:59 UTC. Track eligibility must follow the current track-specific overview; this Rules tab does not itself spell out undergraduate/graduate track qualifications.

## License mapping actually inspected

The repository code `LICENSE` is Apache 2.0. `LICENSE-docs` is CC BY 4.0. The input dataset has a different noncommercial license and additional competition access restrictions. Do not apply the code license to the input data. Existing code licensing is consistent in type with the rules' open-source code requirement; the prose license alone should not be treated as an explicit OSI-approved license for the entire winning submission. An author-approved submission-specific grant and third-party attribution review can address that at publication/award time without changing the repository-wide licenses now.

Full Rules inspection is complete. This records the observed terms and practical implications; it does not certify the user's personal eligibility, ownership of every dependency or agreement acceptance. The required public Kaggle notebook and author authorization still remain before publication/submission.
