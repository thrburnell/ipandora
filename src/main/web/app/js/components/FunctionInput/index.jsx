import React from 'react'
import CentredButton from '../CentredButton'

const FunctionInput = ({ onValidateClick, valid, definition }) => {

  const className = ["panel", "panel-default", valid ? "panel-success" : valid == undefined ? "" : "panel-danger"].join(" ")

  let input
  return (
    <div className={className}>
      <div className="panel-heading">
        <h3 className="panel-title">Function Definition</h3>
      </div>
      <div className="panel-body">
        { valid ? (
        <div className="monospace-font">
          { definition.split("\n").map((e, i) => 
            <span key={i} dangerouslySetInnerHTML={{
              __html: e.replace(/\s/g, '&nbsp;') + "<br />" }} />)
           }
        </div>
          ) : 
          (
        <form>
          <div className="form-group bottom-no-margin">
            <textarea ref={node => { input = node }} className="form-control monospace-font" rows="4" />
          </div>
        </form>
        ) }
      </div>
      {
        valid ? null : (
          <div className="panel-footer clearfix">
            <CentredButton onButtonClick={() => onValidateClick(input.value)} text="Validate"/>
          </div>
        )
      }
    </div>
  )
}

export default FunctionInput

