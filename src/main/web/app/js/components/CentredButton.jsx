import React from 'react'

const CentredButton = ({ onButtonClick, text }) => (
  <div className="col-sm-12 text-center">
    <button type="button" className="btn btn-primary" onClick={ onButtonClick }>
      { text }
    </button>
  </div>
)

export default CentredButton

