## Steps to make pull request (PR)

See also: https://leanprover-community.github.io/contribute/index.html

* Request access to push to mathlib on Zulip
  - e.g. in this thread: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Push.20access

* Do one-time git setup
  - On the command line, run the following two commands, with your name and email substituted in:
```
git config --global user.name "Your Name"
git config --global user.email "youremail@yourdomain.com"
```

* Download Mathlib

* Write some Lean code
  - Try to follow the style guide: https://leanprover-community.github.io/contribute/style.html

* Push to a branch of Mathlib

* Open a pull request

* Wait for review and fix reviewer comments

---

Below is some detailed information for your reference:

## Git Terminology

* `git` is a version control system. It will store changes you made, and will allow you to revert to previous versions of your files.
* All versions of your files are stored in the `git history`.
* A `commit` is a snapshot of the repository. You have to manually make a commit, and can only refer to the state of the repository at each commit.
* Before you commit you can `stage` the files that you want to include in your next commit.
* You have to `push` commits that you make locally on your computer to save them remotely (on `github.com`).
* You can `pull` to download remote commits and get them locally (added by someone else, or added by you on another computer).
* `fetch` is similar to `pull`, but it only downloads the new changes to your git history, but doesn't actually incorporate the changes
* VSCode uses the word `sync` to mean `pull` + `push`.
* A `fork` is your own remote copy of the repository on `github.com` (something like `github.com/<YourUsername>/LeanCourse23`). You cannot write to the main repository (`github.com/fpvandoorn/LeanCourse23`)
* If two people both make independent commits to a repository, you can `merge` the commits to create a new commit that has both changes.
* If both commits make a change to the same (or adjacent) lines of a file, then you will get a `merge conflict` which means you have to decide how to merge these two changes.
  - *If you get a merge conflict*: this means that you modified a file that someone else also modified. `git` should tell you which file(s) have a conflict. The easiest way to solve this is to duplicate (copy/paste) the file(s) with a merge conflict (to have a version with your local changes), and then in the VSCode Source Control tab right-click the file(s) and press `Discard changes`.

## Git Instructions

We will be using git via the interface on VSCode. You can also do it from the command line.

### Getting started

* Create an account on `github.com`
* On the command line, run the following two commands, with your name and email substituted in:
```
git config --global user.name "Your Name"
git config --global user.email "youremail@yourdomain.com"
```
* In VSCode, open this file and add your name and your Uni-ID at the top.
* Save all your open files
* Click on the `Source Control` button (left bar, likely the third button from the top).
* Write a small commit message (what you write is not important, but it should not be empty). Press `Commit`.
* Press `Yes` (or `Always`) on the prompt `There are no staged changes to commit. Would you like to stage all changes and commit them directly?`. This will also commit your changes to all other files, which is fine.
* Press `Sync changes`
* Press `OK` (or `OK, don't show again`) when prompted `This action will pull and push commits from and to "origin/master"`
* In the new window, press `Sign in with browser`
* if needed, sign in to Github
* Press `Authorize git-ecosystem`
* You should now see your branch at `https://github.com/leanprover-community/mathlib4/branches/yours` and you can create a pull request there

### Pushing Later Commits

Pushing another commit after the first one is easy:

* Save all your open files
* Write a small commit message and press `Commit`.
* Press `Sync changes`

### Command-line

If you would like to use Git from your command-line instead, you can use the commands `git pull`, `git add`, `git commit -am "commit message"`, `git push`, `git status`, `git log`, among others. Google for information how to exactly use these commands.
