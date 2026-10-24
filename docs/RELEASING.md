# Release procedure

This document records the manual publication steps for a reviewed release candidate. It does
not authorize a release.

## Before publishing v0.2.0

1. Obtain independent review of the exact release-candidate commit and explicit maintainer
   approval to merge it.
2. Merge the candidate, rerun the local verification gate on the resulting `main`, and verify
   that `v0.1.0` is unchanged.
3. Set the actual publication date in `CITATION.cff`, replace “release candidate” with that date
   in `CHANGELOG.md`, validate both citation files again, and review the resulting commit. The
   date is intentionally absent from the candidate metadata because no GitHub Release has yet
   been published and its publication date has not been decided.
4. On Zenodo, link the maintainer's GitHub account if necessary, open **GitHub**, select **Sync
   now**, find `johannedin/causal-sets-lean`, and enable the repository. Complete this before
   publishing the GitHub Release: Zenodo's integration archives new releases from repositories
   that have already been enabled.
5. Create the signed or annotated `v0.2.0` tag only after separate approval. Publish a GitHub
   Release from that exact tag using the reviewed release notes.
6. In Zenodo's GitHub view, wait for processing to finish. Open the resulting record through its
   DOI, verify the version, creators, ORCID, Apache-2.0 license, related-publication link, archived
   file and checksum, and check **External resources → Archived in** for preservation status.
   Record both the version-specific DOI and the concept DOI.

## Zenodo integration facts

- A public repository is eligible when it is visible to the linked GitHub account and the
  account has the access needed to enable Zenodo's repository webhook. The maintainer must
  perform and verify this account-level setup; repository files cannot enable it.
- Publishing a GitHub Release—not merely creating a tag—is the ingestion trigger documented by
  Zenodo. On the first published Zenodo record, Zenodo assigns one DOI to that exact version and
  a concept DOI representing all versions; later releases receive new version DOIs under the
  same concept.
- The GitHub integration produces a software record from the release source archive. Zenodo's
  current guide describes a single compressed software file, and its public tracker still lists
  inclusion of separately uploaded GitHub release assets as an open request. Do not rely on
  GitHub release attachments being copied into the Zenodo record; verify the actual Zenodo file
  list after ingestion.
- Zenodo reads `.zenodo.json` in preference to `CITATION.cff` when both are present. The JSON file
  therefore carries the richer Zenodo-specific related-publication relation, while
  `CITATION.cff` remains useful for GitHub's citation display. Their shared title, creator,
  ORCID, version, license, description, and keywords must remain consistent.
- The repository does not contain, reserve, or predict a software DOI. DOI values must be copied
  from the successfully published Zenodo record.

## Official documentation checked

- [Linking a GitHub account](https://help.zenodo.org/docs/profile/linking-accounts/)
- [Enabling a repository](https://help.zenodo.org/docs/github/enable-repository/)
- [Describing software and metadata precedence](https://help.zenodo.org/docs/github/describe-software/)
- [Archiving a GitHub release](https://help.zenodo.org/docs/github/archive-software/github-upload/)
- [Zenodo DOI versioning](https://zenodo.org/help/versioning)
- [Zenodo GitHub permissions](https://support.zenodo.org/help/en-gb/24-github-integration/127-which-github-permissions-do-you-request-and-why)

These pages were checked on 2026-10-24. Account linkage and repository enablement remain manual
maintainer actions; this project does not automate them.
