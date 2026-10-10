"use strict";
document.addEventListener('DOMContentLoaded', () => {
    const canvas1 = document.getElementById('matrixCanvas1');
    const ctx1 = canvas1?.getContext('2d');
    const canvas2 = document.getElementById('matrixCanvas2');
    const ctx2 = canvas2?.getContext('2d');
    const colorPicker = document.getElementById('colorPicker');
    const matrixFile1 = document.getElementById('matrixFile1');
    const matrixFile2 = document.getElementById('matrixFile2');
    const matrixSizeSpan1 = document.getElementById('matrixSize1');
    const matrixSizeSpan2 = document.getElementById('matrixSize2');
    const uniqueValuesSpan = document.getElementById('uniqueValues');
    const inputFileList = document.getElementById('inputFileList');
    const outputFileList = document.getElementById('outputFileList');
    let matrix1 = [];
    let matrix2 = [];
    let allUniqueValues = new Set();
    let colorMap = new Map();
    const defaultColors = [
        '#FF0000', '#00FF00', '#0000FF', '#FFFF00', '#FF00FF',
        '#00FFFF', '#FFA500', '#800080', '#008000', '#000080'
    ];
    function parseMatrix(text) {
        const lines = text.trim().split('\n');
        return lines.map(line => line.trim().split(/\s+/).map(Number));
    }
    function findUniqueValues(matrix) {
        const values = new Set();
        for (const row of matrix) {
            for (const val of row) {
                values.add(val);
            }
        }
        return Array.from(values).sort((a, b) => a - b);
    }
    function initColorPickers(values) {
        const currentValues = new Set(values);
        const sameValues = currentValues.size === colorMap.size &&
            Array.from(currentValues).every(v => colorMap.has(v));
        if (sameValues)
            return;
        const newColorMap = new Map();
        for (const value of values) {
            if (colorMap.has(value)) {
                newColorMap.set(value, colorMap.get(value));
            }
            else {
                const index = newColorMap.size % defaultColors.length;
                newColorMap.set(value, defaultColors[index]);
            }
        }
        colorMap = newColorMap;
        if (colorPicker)
            colorPicker.innerHTML = '';
        const sortedValues = Array.from(colorMap.keys()).sort((a, b) => a - b);
        for (const value of sortedValues) {
            const colorItem = document.createElement('div');
            colorItem.className = 'color-item';
            const label = document.createElement('label');
            label.textContent = `Value ${value}:`;
            const input = document.createElement('input');
            input.type = 'color';
            input.value = colorMap.get(value);
            input.className = 'color-swatch';
            input.addEventListener('input', (e) => {
                const target = e.target;
                const val = parseInt(target.dataset.value || '0', 10);
                colorMap.set(val, target.value);
                redrawAll();
            });
            input.dataset.value = String(value);
            colorItem.appendChild(label);
            colorItem.appendChild(input);
            if (colorPicker)
                colorPicker.appendChild(colorItem);
        }
    }
    function drawMatrix(matrix, ctx, sizeSpan) {
        if (!matrix || matrix.length === 0 || matrix[0].length === 0 || !ctx)
            return;
        const rows = matrix.length;
        const cols = matrix[0].length;
        const containerWidth = (ctx.canvas.parentElement?.clientWidth || 800) - 40;
        const cellSize = Math.max(1, Math.min(20, Math.floor(containerWidth / cols)));
        ctx.canvas.width = cols * cellSize;
        ctx.canvas.height = rows * cellSize;
        for (let y = 0; y < rows; y++) {
            for (let x = 0; x < cols; x++) {
                const value = matrix[y][x];
                ctx.fillStyle = colorMap.get(value) || '#000000';
                ctx.fillRect(x * cellSize, y * cellSize, cellSize, cellSize);
            }
        }
        if (sizeSpan)
            sizeSpan.textContent = `${rows} × ${cols}`;
    }
    function redrawAll() {
        drawMatrix(matrix1, ctx1, matrixSizeSpan1);
        drawMatrix(matrix2, ctx2, matrixSizeSpan2);
        if (uniqueValuesSpan)
            uniqueValuesSpan.textContent = String(allUniqueValues.size);
    }
    window.addEventListener('resize', () => {
        if (matrix1.length > 0 || matrix2.length > 0)
            redrawAll();
    });
    function updateUniqueValues() {
        allUniqueValues = new Set([...findUniqueValues(matrix1), ...findUniqueValues(matrix2)]);
        if (allUniqueValues.size > 0)
            initColorPickers(Array.from(allUniqueValues).sort((a, b) => a - b));
        redrawAll();
    }
    function loadMatrix(file, targetMatrix) {
        return new Promise((resolve) => {
            const reader = new FileReader();
            reader.onload = (e) => {
                const fileContent = e.target?.result;
                if (fileContent) {
                    targetMatrix.length = 0;
                    targetMatrix.push(...parseMatrix(fileContent));
                }
                resolve();
            };
            reader.onerror = () => { alert('Error reading file'); resolve(); };
            reader.readAsText(file);
        });
    }
    const loadBtn = document.getElementById('loadBtn');
    if (loadBtn) {
        loadBtn.addEventListener('click', async () => {
            const file1 = matrixFile1?.files?.[0];
            const file2 = matrixFile2?.files?.[0];
            if (!file1 && !file2) {
                alert('Please select at least one matrix file');
                return;
            }
            const originalText = loadBtn.textContent;
            loadBtn.textContent = 'Loading...';
            loadBtn.disabled = true;
            try {
                await Promise.all([
                    file1 ? loadMatrix(file1, matrix1) : Promise.resolve(),
                    file2 ? loadMatrix(file2, matrix2) : Promise.resolve()
                ]);
                updateUniqueValues();
            }
            catch (error) {
                console.error('Error loading matrices:', error);
                alert('Error loading matrices. Please check the console for details.');
            }
            finally {
                loadBtn.textContent = originalText;
                loadBtn.disabled = false;
            }
        });
    }
    if (matrixFile1) {
        matrixFile1.addEventListener('change', (e) => {
            const target = e.target;
            if (inputFileList)
                inputFileList.textContent = target.files?.[0]?.name || '';
        });
    }
    if (matrixFile2) {
        matrixFile2.addEventListener('change', (e) => {
            const target = e.target;
            if (outputFileList)
                outputFileList.textContent = target.files?.[0]?.name || '';
        });
    }
});
