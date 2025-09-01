# Workbench

A powerful Flask-based web application for data manipulation, file processing, and development utilities. Workbench provides a comprehensive suite of tools for working with CSV files, raw text editing, file downloads, and command execution in a modern web interface.

## Features

### 🗂️ File Management
- **File Download**: Download files from URLs with automatic filename detection
- **File Viewing**: View and process files directly from URLs
- **Local File Support**: Handle local files with proper sanitization

### 📊 CSV Editor
- **Interactive CSV Editing**: Full-featured spreadsheet-like interface
- **Pagination**: Handle large CSV files with configurable page sizes
- **Real-time Editing**: Edit cells directly with immediate updates
- **Export Options**: Download edited CSV files
- **Data Validation**: Built-in data type handling and validation

### ✏️ Raw Text Editor
- **Syntax Highlighting**: Support for various file formats
- **Large File Handling**: Efficient processing of large text files
- **Save/Download**: Save changes and download processed files
- **Theme Support**: Dark/light theme switching

### ⚡ Command Execution
- **Terminal Integration**: Execute system commands through the web interface
- **Timeout Protection**: Commands timeout after 30 seconds for safety
- **Output Capture**: View both stdout and stderr output
- **Error Handling**: Comprehensive error reporting

### 🎨 User Interface
- **Modern Design**: Clean, responsive web interface
- **Dark Theme**: Built-in dark mode support
- **Real-time Clock**: Live time and date display
- **Session Management**: Persistent user sessions

## Installation

### Prerequisites
- Python 3.10+
- pip (Python package manager)

### Setup
1. Clone the repository:
   ```bash
   git clone <repository-url>
   cd workbench
   ```

2. Create a virtual environment:
   ```bash
   python -m venv venv
   source venv/bin/activate  # On Windows: venv\Scripts\activate
   ```

3. Install dependencies:
   ```bash
   pip install -r requirements.txt
   ```

## Usage

### Local Development
Run the application locally:
```bash
python workbench.py
```

The application will start on `http://localhost:9000` (or the port specified in the `PORT` environment variable).

### Production Deployment
The application is configured for deployment on platforms like Heroku:

```bash
# Set environment variables
export PORT=5000
export FLASK_ENV=production

# Run with gunicorn
gunicorn workbench:app --bind 0.0.0.0:$PORT
```

## API Endpoints

### Main Interface
- `GET /` - Main application interface
- `POST /` - Handle file downloads and URL processing

### CSV Operations
- `GET /csv-editor` - CSV editor interface
- `GET /csv-edit` - CSV editing with pagination
- `POST /csv-edit` - Update CSV data
- `POST /update-csv-edit` - Real-time CSV cell updates
- `POST /download_csv` - Download CSV files

### Text Editor
- `GET /raw-editor` - Raw text editor interface
- `POST /save_raw` - Save raw text content
- `POST /download_raw` - Download raw text files

### System Operations
- `POST /execute_command` - Execute system commands
- `POST /set-theme` - Change application theme
- `POST /save-settings` - Save user preferences

## Configuration

### Environment Variables
- `PORT` - Server port (default: 9000)
- `FLASK_ENV` - Flask environment (development/production)

### Settings
The application supports various user-configurable settings:
- Theme preferences (dark/light)
- CSV pagination settings
- Editor preferences

## Dependencies

- **Flask 2.3.3** - Web framework
- **pandas 2.0.3** - Data manipulation and analysis
- **numpy 1.24.3** - Numerical computing
- **requests 2.31.0** - HTTP library
- **gunicorn 21.2.0** - WSGI HTTP server

## Security Considerations

- Commands are executed with a 30-second timeout
- File downloads are validated and sanitized
- Session management with secure keys
- Input validation for all user inputs

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Test thoroughly
5. Submit a pull request

## License

This project is open source. Please check the repository for specific licensing information.

## Support

For issues, questions, or contributions, please use the repository's issue tracker.
