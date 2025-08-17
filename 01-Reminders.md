## Here’s the quick sequence to check if your **local** and **remote** repos are in sync:
```
git fetch origin
git status
```
If `git status` says:

```
Your branch is up to date with 'origin/main'
```

—then you’re synced.

To commit a single file:

```bash
git add path/to/file.txt
git commit -m "Updated file"
git push origin main

That stages **only that file**, commits it with your message, and pushes it to `main`.

or - for the whole repo

git add -A 
git commit -m "Latest updates"
git push origin main
```

Here’s a **simple Git cheat sheet** with the essentials:

### **Check Status**

```bash
git status
```

### **Stage & Commit Changes**

```bash
git add <file>      # stage a file
git add .           # stage all changes
git commit -m "message"
```

### **Push Changes**

```bash
git push origin <branch>
```

### **Pull Changes**

```bash
git pull origin <branch>
```

### **Create & Switch Branches**

```bash
git branch <branch>     # create branch
git checkout <branch>   # switch branch
git checkout -b <branch> # create & switch in one step
```

### **Merge Branches**

```bash
git checkout main
git merge <branch>
```

### **View History**

```bash
git log --oneline --graph --all
```

### **Undo Changes**

```bash
git restore <file>      # discard changes
git reset --soft HEAD~1 # undo last commit, keep changes staged
git reset --hard HEAD~1 # undo last commit, discard changes
```