import React from 'react'

const Formula = ({ id, uiId, formula, onFormulaClick }) => (
  <h4 onClick={() => onFormulaClick(id)}>({ uiId }) { formula }</h4>
)

export default Formula

