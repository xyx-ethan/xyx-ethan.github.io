// ===== Note page: sidebar TOC, scroll spy, animations =====

// Theme toggle
document.getElementById('noteThemeToggle').addEventListener('click', function() {
    var html = document.documentElement;
    var current = html.getAttribute('data-theme');
    var next = current === 'dark' ? 'light' : 'dark';
    if (next === 'light') { html.removeAttribute('data-theme'); } else { html.setAttribute('data-theme', 'dark'); }
    localStorage.setItem('theme', next);
});

// Download as PDF (uses browser print-to-PDF; preserves current theme)
var downloadBtn = document.getElementById('noteDownload');
if (downloadBtn) {
    downloadBtn.addEventListener('click', function() {
        // Reveal all fade-animated elements: clear inline opacity/transform
        // that the scroll-reveal JS set, otherwise below-the-fold content
        // prints invisible. Restore after print dialog closes.
        var hidden = document.querySelectorAll('.note-body [data-fade-ready]');
        var savedStyles = [];
        hidden.forEach(function(el) {
            savedStyles.push({
                opacity: el.style.opacity,
                transform: el.style.transform,
                transition: el.style.transition
            });
            el.style.opacity = '';
            el.style.transform = '';
            el.style.transition = '';
        });

        function restore() {
            hidden.forEach(function(el, i) {
                el.style.opacity = savedStyles[i].opacity;
                el.style.transform = savedStyles[i].transform;
                el.style.transition = savedStyles[i].transition;
            });
        }

        if (window.MathJax && MathJax.startup) {
            MathJax.startup.promise.then(function() {
                setTimeout(function() {
                    window.print();
                    setTimeout(restore, 100);
                }, 200);
            });
        } else {
            window.print();
            setTimeout(restore, 100);
        }
    });
}

// Build sidebar TOC from .toc ol links
(function() {
    var tocDiv = document.querySelector('.note-content > .toc');
    if (!tocDiv) return;

    var sidebar = document.querySelector('.note-sidebar');
    if (!sidebar) return;

    var tocList = sidebar.querySelector('.toc-list');
    if (!tocList) return;

    // Copy ALL TOC links from inline TOC to sidebar, prepend section number
    var allLinks = tocDiv.querySelectorAll('li a');
    var sectionNum = 0;
    allLinks.forEach(function(a) {
        sectionNum++;
        var newLi = document.createElement('li');
        var newA = document.createElement('a');
        var rawHref = a.getAttribute('href');
        newA.setAttribute('href', rawHref);

        // Create number span + text
        var numSpan = document.createElement('span');
        numSpan.className = 'toc-num';
        numSpan.textContent = sectionNum + '.';
        newA.appendChild(numSpan);
        newA.appendChild(document.createTextNode(' ' + a.textContent));

        newLi.appendChild(newA);
        tocList.appendChild(newLi);
    });

    // Smooth scroll on click
    tocList.querySelectorAll('a').forEach(function(link) {
        link.addEventListener('click', function(e) {
            e.preventDefault();
            var target = document.querySelector(this.getAttribute('href'));
            if (target) {
                target.scrollIntoView({ behavior: 'smooth', block: 'start' });
            }
        });
    });
})();

// Scroll spy: highlight active TOC item
(function() {
    var tocLinks = document.querySelectorAll('.toc-list a');
    if (!tocLinks.length) return;

    var headings = [];
    tocLinks.forEach(function(link) {
        var href = link.getAttribute('href');
        var id = href.indexOf('#') !== -1 ? href.substring(href.indexOf('#') + 1) : href;
        var el = document.getElementById(id);
        if (el) headings.push({ el: el, link: link });
    });

    function updateActive() {
        var scrollY = window.scrollY;
        var windowH = window.innerHeight;
        var docH = document.documentElement.scrollHeight;

        // If scrolled to bottom, activate last
        if (scrollY + windowH >= docH - 30) {
            tocLinks.forEach(function(l) { l.classList.remove('active'); });
            if (headings.length) headings[headings.length - 1].link.classList.add('active');
            return;
        }

        var current = headings[0]; // default to first
        headings.forEach(function(h) {
            if (h.el.offsetTop - 80 <= scrollY) current = h;
        });

        tocLinks.forEach(function(l) { l.classList.remove('active'); });
        if (current) {
            current.link.classList.add('active');
            // Scroll the active link into view within sidebar
            current.link.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
        }
    }

    window.addEventListener('scroll', updateActive, { passive: true });
    updateActive(); // initial
})();

// Staggered entrance animation for TOC items
(function() {
    if (window.matchMedia('(prefers-reduced-motion: reduce)').matches) return;

    var tocItems = document.querySelectorAll('.toc-list li');
    tocItems.forEach(function(item, i) {
        item.style.opacity = '0';
        item.style.transform = 'translateX(-10px)';
        item.style.transition = 'opacity 0.4s cubic-bezier(0.4,0,0.2,1), transform 0.4s cubic-bezier(0.4,0,0.2,1)';
        setTimeout(function() {
            item.style.opacity = '1';
            item.style.transform = 'translateX(0)';
        }, 150 + i * 50);
    });

    // Fade in sidebar header
    var header = document.querySelector('.note-sidebar-header');
    if (header) {
        header.style.opacity = '0';
        header.style.transform = 'translateY(-8px)';
        header.style.transition = 'opacity 0.5s ease, transform 0.5s ease';
        setTimeout(function() {
            header.style.opacity = '1';
            header.style.transform = 'translateY(0)';
        }, 100);
    }
})();

// Scroll-triggered fade-in for note body content
(function() {
    if (window.matchMedia('(prefers-reduced-motion: reduce)').matches) return;

    var observer = new IntersectionObserver(function(entries) {
        entries.forEach(function(entry) {
            if (entry.isIntersecting) {
                entry.target.style.opacity = '1';
                entry.target.style.transform = 'translateY(0)';
                observer.unobserve(entry.target);
            }
        });
    }, { threshold: 0.08 });

    function observeElements(root) {
        var sel = 'h2, h3, p, ul, ol, pre, table, [class^="card-"], mjx-container[display="true"], .MathJax';
        var elements = (root || document.querySelector('.note-body')).querySelectorAll(sel);
        elements.forEach(function(el) {
            if (el.dataset.fadeReady) return; // skip already observed
            el.dataset.fadeReady = '1';
            el.style.opacity = '0';
            el.style.transform = 'translateY(12px)';
            el.style.transition = 'opacity 0.5s cubic-bezier(0.4,0,0.2,1), transform 0.5s cubic-bezier(0.4,0,0.2,1)';
            observer.observe(el);
        });
    }

    // Initial pass
    observeElements();

    // Re-run after MathJax finishes rendering
    if (window.MathJax && MathJax.startup) {
        MathJax.startup.promise.then(function() {
            observeElements();
        });
    }
})();
