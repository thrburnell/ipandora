import React from 'react'

const FileUpload = ({ onButtonClick }) => {
  let file

  return (
    <div>
      <input type="file" ref={node => { file = node }}/>
      <button onClick={() => onButtonClick(file.files[0])}>Upload</button>
    </div>
  )
}

export default FileUpload

