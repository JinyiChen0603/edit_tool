@echo off
chcp 65001 >nul
echo ============================================================
echo 数学题目编辑器 - Web版
echo ============================================================
echo.
echo 正在检查 Flask...
python -c "import flask" 2>nul
if errorlevel 1 (
    echo Flask 未安装，正在安装...
    pip install flask
    echo.
)

echo 正在启动编辑器...
echo.
python web_editor.py

pause

