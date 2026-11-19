# Equation (10.19) of Navier–Stokes Lemma 10.5

**Troy Winarski · ORCID 0009-0004-5956-3825**  
Public pre-review research release. The companion theorem `NavierStokesR3.Paper1019.equation_10_19` proves the physical pressure-flux estimate by a two-commutator argument. The note gives the hypotheses and the exact Lean declaration on page 2. Independent external reproduction and mathematical review are pending.

**Repository:** This release is intended for `TheRealDubb/navier-stokes-equation-10-19-lean`. **DOI:** not yet assigned. Publication of the repository creates a public record; independent external verification is still pending.

## File inventory and privacy report

This release contains the 14 unchanged Lean companion source files, the technical paper, reproducibility guidance, license texts, citation metadata, and privacy notices. All paths below are relative to the distribution root.

| Publication file | Contents |
|---|---|
| [NavierStokes_Equation_10_19_Submission.pdf](NavierStokes_Equation_10_19_Submission.pdf) | Seven-page technical note. |
| [manuscript.html](manuscript.html) | Editable source for the note. |
| [ATTRIBUTION_AND_AI_DISCLOSURE.md](ATTRIBUTION_AND_AI_DISCLOSURE.md) | Human direction and AI contributions. |
| [LICENSE_STATUS.md](LICENSE_STATUS.md) | Approved licensing scope and third-party exceptions. |
| [LICENSE](LICENSE) | Apache License 2.0 text for the original Lean companion code. |
| [LICENSE-DOCUMENTATION.md](LICENSE-DOCUMENTATION.md) | CC BY 4.0 declaration for original paper and documentation. |
| [NOTICE](NOTICE) | Contributor/provenance attribution for the original Lean work. |
| [CITATION.cff](CITATION.cff) | Machine-readable citation metadata (without an unassigned DOI). |
| [notices/DejaVu-font-notice.txt](notices/DejaVu-font-notice.txt) | Existing notice for font subsets embedded in the PDF. |
| [notices/OpenAI-upstream-LICENSE.txt](notices/OpenAI-upstream-LICENSE.txt) | License of the cited upstream project, supplied for reference. |
| [REPRODUCIBILITY.md](REPRODUCIBILITY.md) | Public inputs, version pins, build instructions and limits of the available evidence. |
| [SHA256SUMS](SHA256SUMS) | SHA-256 manifest of the other files; check before running anything. |
| [README.md](README.md) | This inventory and privacy report. |

The remaining 14 files are the verified Lean companion sources:

```text
lean/EssentialEnergy.lean
lean/FluxEnvelope.lean
lean/Lemma105PaperFlux.lean
lean/LocalizedFluxTensor.lean
lean/MixedCommutator.lean
lean/MixedKernelPair.lean
lean/MixedRieszCommutator.lean
lean/Paper1019.lean
lean/Paper1019Quantitative.lean
lean/PaperFluxDecomposition.lean
lean/PaperFluxScaling.lean
lean/PaperFluxSlice.lean
lean/PaperFluxTests.lean
lean/PaperFluxZero.lean
```

## Checks performed

- Compared all 14 distributed Lean files directly with their verified source entries in the private proof archive and checked their recorded SHA-256 values. Rechecked the two private archives against their pre-existing digests. The public manuscript updates the directions for locating and reproducing the proof. Its theorem, assumptions, equations and proof discussion match the verified submission.
- Inspected the complete public file list, all text files, source comments, license notices, documentation commands and links. Scanned for the originating account and workspace identifiers, absolute local paths, private contact details and recognizable credentials. No originating username, private workspace path or credential was found.
- Inspected all seven visible PDF pages, the author information, 61 PDF objects, 17 decoded streams, 14 HTTPS link annotations and 126 name records in five embedded fonts. Checked for attachments, incremental revisions, active content and hidden metadata. Reviewed the editable HTML for hidden content, local references and active scripts. The author and ORCID, cited researchers and public repository handles, and third-party licensing credits and contacts are intentional public information.
- Compared the ZIP’s complete member list and extracted bytes with the approved directory and verified every manifest entry. Entries use relative names, uniform timestamps and permissions, and empty comments and extra fields. There are no nested archives, Git histories, compiled Lean objects, historical logs, local environment records or standalone scripts.
- Inspected both the ZIP’s local file headers and its central directory. Checked the distribution files and ZIP for alternate filesystem data streams. All contain only their primary data stream.

This review covers the files in this distribution. The private verification and review archives are held separately. Rebuilding from the public inputs requires fetching the pinned external sources. The licensing choice has been approved for the newly contributed materials. Independent reproduction and scholarly review remain pending.
