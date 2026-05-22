.PHONY: test lint typecheck figures paper clean help

help:
	@echo "Targets:"
	@echo "  test      Run the pytest suite."
	@echo "  lint      Run ruff and mypy (strict)."
	@echo "  typecheck Run mypy only."
	@echo "  figures   Regenerate plots in visualizations/ (no-op until Phase 1)."
	@echo "  paper     Build formal/main.tex to PDF via latexmk."
	@echo "  clean     Remove Python, mypy, ruff, pytest, and LaTeX build artifacts."

test:
	pytest

lint:
	ruff check .
	mypy

typecheck:
	mypy

figures:
	@echo "No figures yet; populated as Phase 1 milestones close."

paper:
	cd formal && latexmk -pdf main.tex

clean:
	rm -rf .pytest_cache .mypy_cache .ruff_cache build dist *.egg-info
	find . -type d -name "__pycache__" -prune -exec rm -rf {} +
	find . -type f -name "*.pyc" -delete
	-cd formal && latexmk -C >/dev/null 2>&1
